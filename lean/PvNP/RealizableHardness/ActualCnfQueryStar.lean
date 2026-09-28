import PvNP.RealizableHardness.ActualGrassmannQueryCompiled
import Complexitylib.SAT.ThreeCNF
import Mathlib.Data.ZMod.Basic

/-!
Clause-gated query stars for a 3CNF.

Each clause has a private center and a private port for every leaf. An edge
is a clause index, a witness index in `Fin 3`, and a shift in `(ZMod R)^m`.
Acceptance equates each leaf's first component with the center's first
component plus that leaf's shift, so each labeling accepts at most one shift
of each clause-witness pair. The uniform score is therefore at most `R^{-m}`.

A satisfying assignment supplies, inside the proof, a labeling that accepts
the zero shift of one witness on every clause. That labeling does not accept
every shift, and when `m > 0` and `R > 1` every labeling has score strictly
below 1, including on satisfiable formulas. For every large leaf bound the
same pair holds at `RBlock` and `certifiedM`: one zero-shift witness accepts,
every labeling scores at most `RBlock^{-certifiedM}`, and no labeling accepts
every edge. The accepting-product hypothesis therefore fails on satisfiable
inputs. Ports are not shared, so the same counting bound holds on
unsatisfiable formulas. This file does not prove that a failing literal
rejects every shift, does not prove `compile`, does not instantiate the
q-fold product, and does not build a `SeededMap` or discharge `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualCnfQueryStar

open ActualGrassmannQueryCompiled
open ActualModifiedPcpCompiled
open ActualCompiledProduct
open ActualCertifiedManuscriptParameters
open ActualCmmsaParameterReconciliation
open ActualHeadlineParameters
open StarListDecoding
open StarFormulaInterface
open StarCmmsaSemantics
open ActualFormulaProduct
open Complexity
open Complexity.SAT
open scoped BigOperators

set_option autoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev QSym (R : Nat) := ZMod R × Fin 2

abbrev QueryVtx (φ : CNF) (m : Nat) := Fin φ.length × Fin m ⊕ Fin φ.length

def qPort {φ : CNF} {m : Nat} (c : Fin φ.length) (i : Fin m) : QueryVtx φ m :=
  Sum.inl (c, i)

def qCenter {φ : CNF} {m : Nat} (c : Fin φ.length) : QueryVtx φ m :=
  Sum.inr c

abbrev qSigma {φ : CNF} {m R : Nat} : QueryVtx φ m → Type := fun _ => QSym R

abbrev QEdge (φ : CNF) (m R : Nat) :=
  Fin φ.length × Fin 3 × (Fin m → ZMod R)

def edgeClause {φ : CNF} {m R : Nat} (e : QEdge φ m R) : Fin φ.length := e.1

def edgeWitness {φ : CNF} {m R : Nat} (e : QEdge φ m R) : Fin 3 := e.2.1

def edgeShift {φ : CNF} {m R : Nat} (e : QEdge φ m R) : Fin m → ZMod R := e.2.2

def nVars (φ : CNF) : Nat := φ.maxVar + 1

theorem lit_var_lt {φ : CNF} {c : Clause} {ℓ : Lit} (hc : c ∈ φ) (hℓ : ℓ ∈ c) :
    ℓ.var < nVars φ :=
  Nat.lt_succ_of_le (le_trans (Clause.var_le_maxVar hℓ) (CNF.clause_maxVar_le_maxVar hc))

def clauseNth (c : Clause) (hc : c.length = 3) (k : Fin 3) : Lit :=
  c.get ⟨k.val, by omega⟩

def clauseLit {φ : CNF} (h3 : φ.Is3CNF) (c : Fin φ.length) (j : Fin 3) : Lit :=
  clauseNth (List.get φ c) (h3 _ (List.get_mem φ c)) j

def encBit (b : Bool) : Fin 2 := if b then 1 else 0

def holdsLit (ℓ : Lit) (bit : Fin 2) : Bool :=
  (bit.val == 1) == ℓ.sign

def gateBit {m : Nat} (k : Fin 3) (i : Fin m) (ℓ : Lit) (bit : Fin 2) : Fin 2 :=
  if i.val = k.val then (if holdsLit ℓ bit then 1 else 0) else 1

def qLeaf {φ : CNF} {m : Nat} (c : Fin φ.length) (i : Fin m) : QueryVtx φ m :=
  qPort c i

def qProj {φ : CNF} {m R : Nat} (h3 : φ.Is3CNF) (c : Fin φ.length) (k : Fin 3)
    (σ : Fin m → ZMod R) (i : Fin m) (a : QSym R) : QSym R :=
  if h : i.val < 3 then
    (a.1 + σ i, gateBit k i (clauseLit h3 c ⟨i.val, h⟩) a.2)
  else
    (a.1 + σ i, 1)

def qStar {φ : CNF} {m R : Nat} (h3 : φ.Is3CNF) (e : QEdge φ m R) :
    Star (QueryVtx φ m) (qSigma (R := R)) m where
  center := qCenter (edgeClause e)
  leaf i := qLeaf (edgeClause e) i
  projection i := qProj h3 (edgeClause e) (edgeWitness e) (edgeShift e) i
  separated i := by
    simp [qCenter, qLeaf, qPort]

abbrev qEdges {φ : CNF} {m R : Nat} (h3 : φ.Is3CNF) : QEdge φ m R →
    Star (QueryVtx φ m) (qSigma (R := R)) m :=
  qStar h3

def zeroShift {m R : Nat} : Fin m → ZMod R := fun _ => 0

theorem clauseEval_or3 (c : Clause) (hc : c.length = 3) (α : Assignment) :
    Clause.eval α c =
      (Lit.eval α (c.get ⟨0, by omega⟩) ||
        (Lit.eval α (c.get ⟨1, by omega⟩) ||
          Lit.eval α (c.get ⟨2, by omega⟩))) := by
  cases c with
  | nil => simp at hc
  | cons a t =>
      have ht : t.length = 2 := by simpa using hc
      cases t with
      | nil => simp at ht
      | cons b u =>
          have hu : u.length = 1 := by simpa using ht
          cases u with
          | nil => simp at hu
          | cons d v =>
              have hv : v.length = 0 := by simpa using hu
              have hvnil : v = [] := List.length_eq_zero_iff.mp hv
              subst hvnil
              simp [Clause.eval, List.any_cons, List.any_nil, Bool.or_false]

theorem exists_witness_lit {φ : CNF} (h3 : φ.Is3CNF) (α : Assignment)
    (c : Fin φ.length) (hc : Clause.eval α (List.get φ c) = true) :
    ∃ k : Fin 3, Lit.eval α (clauseLit h3 c k) = true := by
  have hlen : (List.get φ c).length = 3 := h3 _ (List.get_mem φ c)
  have hor := clauseEval_or3 (List.get φ c) hlen α
  rw [hor] at hc
  cases h0 : Lit.eval α ((List.get φ c).get ⟨0, by omega⟩)
  · cases h1 : Lit.eval α ((List.get φ c).get ⟨1, by omega⟩)
    · have h2 : Lit.eval α ((List.get φ c).get ⟨2, by omega⟩) = true := by
        rw [h0, h1] at hc
        simpa using hc
      exact ⟨2, by simpa [clauseLit, clauseNth] using h2⟩
    · exact ⟨1, by simpa [clauseLit, clauseNth] using h1⟩
  · exact ⟨0, by simpa [clauseLit, clauseNth] using h0⟩

def encLabel {φ : CNF} {m R : Nat} (h3 : φ.Is3CNF) (α : Assignment) :
    QueryVtx φ m → QSym R :=
  fun v =>
    match v with
    | Sum.inl (c, i) =>
        if h : i.val < 3 then
          (0, encBit (α.get (clauseLit h3 c ⟨i.val, h⟩).var))
        else
          (0, 1)
    | Sum.inr _ => (0, 1)

theorem holds_encBit (ℓ : Lit) (b : Bool) :
    holdsLit ℓ (encBit b) = (b == ℓ.sign) := by
  cases b <;> cases h : ℓ.sign <;> simp [holdsLit, encBit, h, Nat.mod_eq_of_lt]

theorem litEval_iff_holds {φ : CNF} (h3 : φ.Is3CNF) (α : Assignment)
    (c : Fin φ.length) (j : Fin 3) :
    holdsLit (clauseLit h3 c j) (encBit (α.get (clauseLit h3 c j).var)) =
      Lit.eval α (clauseLit h3 c j) := by
  rw [holds_encBit, Lit.eval, Assignment.get]

theorem enc_proj_zero {φ : CNF} {m R : Nat} [NeZero R] (h3 : φ.Is3CNF)
    (α : Assignment) (c : Fin φ.length) (k : Fin 3)
    (hlit : Lit.eval α (clauseLit h3 c k) = true) (i : Fin m) :
    qProj (R := R) h3 c k (zeroShift (R := R)) i
        (encLabel (m := m) (R := R) h3 α (qLeaf c i)) =
      encLabel (m := m) (R := R) h3 α (qCenter c) := by
  simp only [qProj, qLeaf, qPort, qCenter, encLabel, zeroShift, add_zero]
  by_cases hi : i.val < 3
  · simp only [hi, dite_true]
    by_cases hk : i.val = k.val
    · have hkf : (⟨i.val, hi⟩ : Fin 3) = k := Fin.ext hk
      have hhold : holdsLit (clauseLit h3 c ⟨i.val, hi⟩)
          (encBit (α.get (clauseLit h3 c ⟨i.val, hi⟩).var)) = true := by
        rw [litEval_iff_holds]
        simpa [hkf] using hlit
      have hhold' : holdsLit (clauseLit h3 c k)
          (encBit (α.get (clauseLit h3 c k).var)) = true := by
        simpa [hkf] using hhold
      simp [gateBit, hk, hhold']
    · simp [gateBit, hk]
  · simp [hi]

theorem enc_accepts_witness {φ : CNF} {m R : Nat} [NeZero R] (h3 : φ.Is3CNF)
    (α : Assignment) (c : Fin φ.length) (k : Fin 3)
    (h : Lit.eval α (clauseLit h3 c k) = true) :
    (qStar (m := m) (R := R) h3 (c, k, zeroShift (m := m) (R := R))).accepts
      (encLabel (m := m) (R := R) h3 α) := by
  intro i
  simpa [qStar, qCenter, qLeaf, edgeClause, edgeWitness, edgeShift] using
    enc_proj_zero (m := m) (R := R) h3 α c k h i

theorem enc_accepts_of_sat {φ : CNF} {m R : Nat} [NeZero R] (_hm : 3 ≤ m)
    (h3 : φ.Is3CNF) (α : Assignment) (hα : CNF.eval α φ = true) (c : Fin φ.length) :
    ∃ k : Fin 3,
      (qStar (m := m) (R := R) h3 (c, k, zeroShift (m := m) (R := R))).accepts
        (encLabel (m := m) (R := R) h3 α) := by
  have hc : Clause.eval α (List.get φ c) = true := by
    have hall : φ.all (Clause.eval α) = true := by simpa [CNF.eval] using hα
    exact List.all_eq_true.mp hall _ (List.get_mem φ c)
  obtain ⟨k, hk⟩ := exists_witness_lit h3 α c hc
  exact ⟨k, enc_accepts_witness (m := m) (R := R) h3 α c k hk⟩

theorem edge_card {φ : CNF} {m R : Nat} [NeZero R] :
    Fintype.card (QEdge φ m R) = φ.length * (3 * R ^ m) := by
  unfold QEdge
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_fun, Fintype.card_fin]
  have hR : Fintype.card (ZMod R) = R := by
    rw [Fintype.card_eq_nat_card, Nat.card_zmod]
  rw [hR]

theorem accepts_determines_shift {φ : CNF} {m R : Nat} [NeZero R]
    (h3 : φ.Is3CNF) (l : QueryVtx φ m → QSym R) (e : QEdge φ m R)
    (hacc : (qStar h3 e).accepts l) :
    edgeShift e = fun i => (l (qCenter (edgeClause e))).1 - (l (qLeaf (edgeClause e) i)).1 := by
  funext i
  have hi := hacc i
  simp only [qStar, qProj, qLeaf, qCenter] at hi
  by_cases h : i.val < 3
  · simp only [h, dite_true] at hi
    have hfst := congrArg Prod.fst hi
    exact eq_sub_of_add_eq' hfst
  · simp only [h, dite_false] at hi
    have hfst := congrArg Prod.fst hi
    exact eq_sub_of_add_eq' hfst

theorem accepting_card_le {φ : CNF} {m R : Nat} [NeZero R]
    (h3 : φ.Is3CNF) (_hφ : 0 < φ.length) (l : QueryVtx φ m → QSym R) :
    (Finset.univ.filter fun e : QEdge φ m R => (qStar h3 e).accepts l).card ≤
      φ.length * 3 := by
  classical
  let s := Finset.univ.filter fun e : QEdge φ m R => (qStar h3 e).accepts l
  let f : QEdge φ m R → Fin φ.length × Fin 3 := fun e => (edgeClause e, edgeWitness e)
  have hinj : ∀ e1 ∈ s, ∀ e2 ∈ s, f e1 = f e2 → e1 = e2 := by
    intro e1 he1 e2 he2 hfe
    have ha1 : (qStar h3 e1).accepts l := by simpa [s] using he1
    have ha2 : (qStar h3 e2).accepts l := by simpa [s] using he2
    have h1 := accepts_determines_shift h3 l e1 ha1
    have h2 := accepts_determines_shift h3 l e2 ha2
    obtain ⟨hc, hk⟩ := Prod.ext_iff.mp hfe
    have hc' : edgeClause e1 = edgeClause e2 := by simpa [f, edgeClause] using hc
    have hk' : edgeWitness e1 = edgeWitness e2 := by simpa [f, edgeWitness] using hk
    refine Prod.ext hc' (Prod.ext hk' ?_)
    change edgeShift e1 = edgeShift e2
    rw [h1, h2, hc']
  have hsub : ∀ e ∈ s, f e ∈ (Finset.univ : Finset (Fin φ.length × Fin 3)) := by
    intro _ _; exact Finset.mem_univ _
  have hcard := Finset.card_le_card_of_injOn f hsub hinj
  simpa [s, Fintype.card_prod, Fintype.card_fin] using hcard

theorem score_div {φ : CNF} {m R : Nat} [NeZero R] (h3 : φ.Is3CNF)
    (hφ : 0 < φ.length) (l : QueryVtx φ m → QSym R) :
    score uniformEdge (qEdges h3) l =
      ((Finset.univ.filter fun e : QEdge φ m R => (qStar h3 e).accepts l).card : ℝ) /
        (Fintype.card (QEdge φ m R) : ℝ) := by
  classical
  let : Nonempty (QEdge φ m R) := ⟨(⟨0, hφ⟩, 0, fun _ => 0)⟩
  unfold score eventMass uniformEdge
  rw [← Finset.sum_filter]
  simp only [one_div, Finset.sum_const, nsmul_eq_mul]
  have hc : (Fintype.card (QEdge φ m R) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (QEdge φ m R) ≠ 0)
  field_simp [hc]

theorem cnfQuery_score_le {φ : CNF} {m R : Nat} [NeZero R]
    (h3 : φ.Is3CNF) (hφ : 0 < φ.length) (l : QueryVtx φ m → QSym R) :
    score uniformEdge (qEdges h3) l ≤ ((R : ℝ) ^ m)⁻¹ := by
  rw [score_div h3 hφ l]
  have hnum := accepting_card_le h3 hφ l
  have hden : (Fintype.card (QEdge φ m R) : ℝ) =
      (φ.length : ℝ) * ((3 : ℝ) * (R : ℝ) ^ m) := by
    exact_mod_cast edge_card (φ := φ) (m := m) (R := R)
  have hpos3 : (0 : ℝ) < (φ.length * 3 : ℝ) := by
    exact_mod_cast (Nat.mul_pos hφ (by decide : 0 < 3))
  have hposR : (0 : ℝ) < (R : ℝ) ^ m := by
    exact pow_pos (by exact_mod_cast (NeZero.pos R)) _
  rw [hden]
  have hsc : ((Finset.univ.filter fun e : QEdge φ m R =>
      (qStar h3 e).accepts l).card : ℝ) ≤ (φ.length : ℝ) * 3 := by
    exact_mod_cast hnum
  have hdenPos : (0 : ℝ) ≤ (φ.length : ℝ) * ((3 : ℝ) * (R : ℝ) ^ m) :=
    (mul_pos (by exact_mod_cast hφ) (mul_pos (by norm_num) hposR)).le
  have hdiv := div_le_div_of_nonneg_right hsc hdenPos
  have hform : ((φ.length : ℝ) * 3) / ((φ.length : ℝ) * ((3 : ℝ) * (R : ℝ) ^ m)) =
      ((R : ℝ) ^ m)⁻¹ := by
    have h3nz : (3 : ℝ) ≠ 0 := by norm_num
    field_simp [hpos3.ne', h3nz, hposR.ne']
  exact le_trans hdiv (le_of_eq hform)

theorem cnfQuery_score_lt_one {φ : CNF} {m R : Nat} [NeZero R]
    (hm : 0 < m) (hR : 1 < R) (h3 : φ.Is3CNF) (hφ : 0 < φ.length)
    (l : QueryVtx φ m → QSym R) :
    score uniformEdge (qEdges h3) l < 1 := by
  refine lt_of_le_of_lt (cnfQuery_score_le h3 hφ l) ?_
  have hpow : (1 : ℝ) < (R : ℝ) ^ m := by
    exact_mod_cast (Nat.one_lt_pow hm.ne' hR)
  exact (inv_lt_one₀ (by positivity)).mpr hpow

/-- On a satisfiable nonempty 3CNF the encoding accepts one zero-shift witness
edge of every clause, and every labeling still has uniform score strictly below 1. -/
theorem cnfQuery_sat_accepts_and_score_lt_one {φ : CNF} {m R : Nat} [NeZero R]
    (hm : 3 ≤ m) (hR : 1 < R) (h3 : φ.Is3CNF) (hφ : 0 < φ.length)
    (α : Assignment) (hα : CNF.eval α φ = true) (c : Fin φ.length) :
    (∃ k : Fin 3,
        (qStar (m := m) (R := R) h3 (c, k, zeroShift (m := m) (R := R))).accepts
          (encLabel (m := m) (R := R) h3 α)) ∧
      ∀ l : QueryVtx φ m → QSym R, score uniformEdge (qEdges h3) l < 1 := by
  refine ⟨enc_accepts_of_sat hm h3 α hα c, ?_⟩
  intro l
  exact cnfQuery_score_lt_one (lt_of_lt_of_le (by decide : 0 < 3) hm) hR h3 hφ l

theorem cnfRBlock_pos (L m : Nat) : 0 < RBlock L m := by
  unfold RBlock
  exact Nat.two_pow_pos _

instance cnfRBlock_neZero (L m : Nat) : NeZero (RBlock L m) :=
  ⟨(cnfRBlock_pos L m).ne'⟩

theorem cnfQuery_score_le_rBlock {φ : CNF} (L : Nat) (h3 : φ.Is3CNF)
    (hφ : 0 < φ.length)
    (l : QueryVtx φ (certifiedM L) → QSym (RBlock L (certifiedM L))) :
    score uniformEdge
        (qEdges (m := certifiedM L) (R := RBlock L (certifiedM L)) h3) l ≤
      ((RBlock L (certifiedM L) : ℝ) ^ certifiedM L)⁻¹ :=
  cnfQuery_score_le (m := certifiedM L) (R := RBlock L (certifiedM L)) h3 hφ l

theorem cnfQuery_score_eq_one_of_accepts {φ : CNF} {m R : Nat} [NeZero R]
    (h3 : φ.Is3CNF) (hφ : 0 < φ.length) (l : QueryVtx φ m → QSym R)
    (hall : ∀ e, (qStar h3 e).accepts l) :
    score uniformEdge (qEdges h3) l = 1 := by
  let : Nonempty (QEdge φ m R) := ⟨(⟨0, hφ⟩, 0, fun _ => 0)⟩
  rw [score_div h3 hφ l]
  have hfilter :
      (Finset.univ.filter fun e : QEdge φ m R => (qStar h3 e).accepts l) =
        Finset.univ := by
    ext e
    simp [hall e]
  rw [hfilter, Finset.card_univ]
  exact div_self
    (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card (QEdge φ m R) ≠ 0))

theorem cnfQuery_no_total_accept {φ : CNF} {m R : Nat} [NeZero R]
    (hm : 0 < m) (hR : 1 < R) (h3 : φ.Is3CNF) (hφ : 0 < φ.length) :
    ¬ ∃ l : QueryVtx φ m → QSym R, ∀ e, (qStar h3 e).accepts l := by
  rintro ⟨l, hall⟩
  exact (cnfQuery_score_lt_one hm hR h3 hφ l).ne
    (cnfQuery_score_eq_one_of_accepts h3 hφ l hall)

/-- For every large `L`, a satisfiable nonempty 3CNF has one accepting
zero-shift witness at `RBlock` and `certifiedM`, every labeling scores at most
`RBlock^{-certifiedM}`, and no labeling accepts every edge. -/
theorem cnfQuery_sat_rBlock_partial_no_total :
    ∃ L0, ∀ L, L0 ≤ L →
      1 < RBlock L (certifiedM L) ∧ 3 ≤ certifiedM L ∧
      ∀ {φ : CNF} (h3 : φ.Is3CNF) (_hφ : 0 < φ.length) (α : Assignment)
        (_hα : CNF.eval α φ = true) (c : Fin φ.length),
        (∃ k : Fin 3,
            (qStar (m := certifiedM L) (R := RBlock L (certifiedM L)) h3
                (c, k, zeroShift (m := certifiedM L)
                  (R := RBlock L (certifiedM L)))).accepts
              (encLabel (m := certifiedM L) (R := RBlock L (certifiedM L)) h3 α)) ∧
          (∀ l : QueryVtx φ (certifiedM L) → QSym (RBlock L (certifiedM L)),
            score uniformEdge
                (qEdges (m := certifiedM L) (R := RBlock L (certifiedM L)) h3) l ≤
              ((RBlock L (certifiedM L) : ℝ) ^ certifiedM L)⁻¹) ∧
          ¬ ∃ l : QueryVtx φ (certifiedM L) → QSym (RBlock L (certifiedM L)),
            ∀ e, (qEdges (m := certifiedM L) (R := RBlock L (certifiedM L)) h3 e).accepts
              l := by
  obtain ⟨L0, hL0⟩ := certified_parameters_eventually 256
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, _, hM, hAd, hmcert, _⟩ := hL0 L hL
  rcases hAd with ⟨_, _, _, _, _, _, _, hsrc, _⟩
  have hm3 : 3 ≤ certifiedM L := by
    rw [hmcert]
    exact le_trans (by decide : 3 ≤ 256) hM
  have hR : 1 < RBlock L (certifiedM L) := by
    rw [hmcert]
    have hsm : m + 2 ≤ hBlock L m := by simpa [manuscriptSourceFloor] using hsrc
    have hblock : 258 ≤ hBlock L m := (Nat.add_le_add_right hM 2).trans hsm
    have hexp : 2 ≤ 2 * hBlock L m := by
      exact Nat.mul_le_mul_left 2 (le_trans (by decide : 1 ≤ 258) hblock)
    have hpow : 4 ≤ RBlock L m := by
      unfold RBlock
      have htwo : 2 ^ 2 ≤ 2 ^ (2 * hBlock L m) :=
        Nat.pow_le_pow_right (by decide : 1 ≤ 2) hexp
      simpa using htwo
    exact (by decide : 1 < 4).trans_le hpow
  refine ⟨hR, hm3, ?_⟩
  intro φ h3 hφ α hα c
  refine ⟨enc_accepts_of_sat (m := certifiedM L) (R := RBlock L (certifiedM L))
      hm3 h3 α hα c,
    fun l => cnfQuery_score_le_rBlock L h3 hφ l,
    cnfQuery_no_total_accept (m := certifiedM L) (R := RBlock L (certifiedM L))
      (lt_of_lt_of_le (by decide : 0 < 3) hm3) hR h3 hφ⟩

end

end PvNP.RealizableHardness.ActualCnfQueryStar
