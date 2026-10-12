import PvNP.RealizableHardness.ActualOccurrenceCounts
import PvNP.RealizableHardness.ActualOccurrenceDegree
import PvNP.RealizableHardness.ActualStarQuestionSupport
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! The occurrence-sensitive degree input for the ordered-question mass bridge. -/
namespace PvNP.RealizableHardness.ActualQuestionMassBridge
open ActualOccurrenceAllocation
open ActualOccurrenceDegree
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
variable {X E : Type*} [Fintype X] [Fintype E]
  [DecidableEq X] [DecidableEq E]

theorem rowId_incidence_card_eq_degree
    {N m : Nat} (I : Instance N m) (x : I.GlobalVar) :
    ((Finset.univ : Finset I.RowId).filter (fun q => x ∈ I.support q)).card =
      ActualOccurrenceDegree.degree I x := by
  calc
    ((Finset.univ : Finset I.RowId).filter (fun q => x ∈ I.support q)).card =
        ((I.rowIndices.toFinset).filter (fun q => x ∈ I.support q)).card := by
      rw [I.rowIndices_toFinset]
    _ = I.rowIndices.countP (fun q => decide (x ∈ I.support q)) := by
      convert
        (List.Nodup.card_eq_countP (l := I.rowIndices)
          (P := fun q : I.RowId => x ∈ I.support q) I.rowIndices_nodup) using 1
      apply congrArg (fun p => I.rowIndices.countP p)
      funext q
      by_cases h : x ∈ I.support q <;> simp [h]
    _ = ActualOccurrenceDegree.degree I x := by
      unfold ActualOccurrenceDegree.degree
      rw [I.rows_eq_map, List.countP_map]
      apply congrArg (fun p => I.rowIndices.countP p)
      funext q
      simp [ActualOccurrenceDegree.containsVar, I.support_eq]

theorem rowId_incidence_card_le_four
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (x : I.GlobalVar) :
    ((Finset.univ : Finset I.RowId).filter (fun q => x ∈ I.support q)).card ≤ 4 := by
  rw [rowId_incidence_card_eq_degree]
  exact ActualOccurrenceDegree.degree_le_four I x

def rowConflict
    (row : E → Finset X) (e f : E) : Prop :=
  e = f ∨
  ¬ Disjoint (row e) (row f) ∨
  ∃ g : E, ∃ x ∈ row e, ∃ y ∈ row f,
    x ∈ row g ∧ y ∈ row g

def GoodOrderedQuestion
    {X E : Type*} [Fintype X] [Fintype E]
    [DecidableEq X] [DecidableEq E]
    {J : Nat} (row : E → Finset X) (u : Fin J → E) : Prop :=
  Function.Injective u ∧
    ActualStarQuestionSupport.GoodQuestion row (Finset.univ.image u)

theorem not_goodOrderedQuestion_iff_conflicting_pair
    {X E : Type*} [Fintype X] [Fintype E]
    [DecidableEq X] [DecidableEq E]
    {J : Nat} (row : E → Finset X) (u : Fin J → E) :
    ¬ GoodOrderedQuestion row u ↔
      ∃ i j : Fin J, i ≠ j ∧ rowConflict row (u i) (u j) := by
  classical
  constructor
  · intro hbad
    by_contra hnone
    push_neg at hnone
    apply hbad
    refine ⟨?_, ?_⟩
    · intro i j heq
      by_contra hij
      exact hnone i j hij (Or.inl heq)
    · constructor
      · intro e he f hf hef
        rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
        rcases Finset.mem_image.mp hf with ⟨j, hj, rfl⟩
        have hij : i ≠ j := by
          intro hij
          apply hef
          exact congrArg u hij
        by_contra hdis
        exact hnone i j hij (Or.inr (Or.inl hdis))
      · intro e he f hf hef g x hx y hy hxg hyg
        rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
        rcases Finset.mem_image.mp hf with ⟨j, hj, rfl⟩
        have hij : i ≠ j := by
          intro hij
          apply hef
          exact congrArg u hij
        exact hnone i j hij
          (Or.inr (Or.inr ⟨g, x, hx, y, hy, hxg, hyg⟩))
  · rintro ⟨i, j, hij, hconflict⟩ hgood
    rcases hgood with ⟨hinj, hquestion⟩
    rcases hconflict with heq | hdis | ⟨g, x, hx, y, hy, hxg, hyg⟩
    · exact hij (hinj heq)
    · have hi : u i ∈ Finset.univ.image u := Finset.mem_image.mpr ⟨i, by simp, rfl⟩
      have hj : u j ∈ Finset.univ.image u := Finset.mem_image.mpr ⟨j, by simp, rfl⟩
      have hne : u i ≠ u j := by
        intro heq'
        exact hij (hinj heq')
      exact hdis (hquestion.1 hi hj hne)
    · have hi : u i ∈ Finset.univ.image u := Finset.mem_image.mpr ⟨i, by simp, rfl⟩
      have hj : u j ∈ Finset.univ.image u := Finset.mem_image.mpr ⟨j, by simp, rfl⟩
      have hne : u i ≠ u j := by
        intro heq'
        exact hij (hinj heq')
      exact hquestion.2 (u i) hi (u j) hj hne g x hx y hy hxg hyg

def pairConflictSet
    {X E : Type*} [Fintype X] [Fintype E]
    [DecidableEq X] [DecidableEq E]
    {J : Nat} (row : E → Finset X) (i j : Fin J) :
    Finset (Fin J → E) :=
  Finset.univ.filter (fun u => rowConflict row (u i) (u j))

theorem pairConflictSet_card_le
    {X E : Type*} [Fintype X] [Fintype E]
    [DecidableEq X] [DecidableEq E]
    {J : Nat} (row : E → Finset X) (C : Nat)
    (hconflict : ∀ e,
      ((Finset.univ : Finset E).filter
        (rowConflict row e)).card ≤ C)
    (i j : Fin J) (hij : i ≠ j) :
    (pairConflictSet row i j).card ≤
      C * (Fintype.card E) ^ (J - 1) := by
  classical
  let K : Type := {k : Fin J // k ≠ i ∧ k ≠ j}
  let encode : (Fin J → E) → E × E × (K → E) :=
    fun u => (u i, u j, fun k => u k.1)
  have hencode : Function.Injective encode := by
    intro u v huv
    funext k
    by_cases hki : k = i
    · simpa [hki] using congrArg Prod.fst huv
    · by_cases hkj : k = j
      · simpa [hkj] using congrArg (fun z => z.2.1) huv
      · have htail := congrArg (fun z => z.2.2 ⟨k, hki, hkj⟩) huv
        exact htail
  let target : Finset (E × E × (K → E)) :=
    (Finset.univ : Finset E).biUnion (fun e =>
      ((Finset.univ : Finset E).filter (rowConflict row e)).biUnion (fun f =>
        (Finset.univ : Finset (K → E)).image (fun t => (e, f, t))))
  have himage : (pairConflictSet row i j).image encode ⊆ target := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨u, hu, rfl⟩
    rcases Finset.mem_filter.mp hu with ⟨_, hconflict⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨u i, Finset.mem_univ _, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨u j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hconflict⟩, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨fun k => u k.1, Finset.mem_univ _, rfl⟩
  have hKcard : Fintype.card K = J - 2 := by
    rw [Fintype.card_subtype]
    have hfilter :
        ({k : Fin J | k ≠ i ∧ k ≠ j} : Finset (Fin J)) =
          (Finset.univ.erase i).erase j := by
      ext k
      simp [and_comm]
    rw [hfilter]
    rw [Finset.card_erase_of_mem
      (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]
    omega
  have htailcard : (Finset.univ : Finset (K → E)).card =
      (Fintype.card E) ^ (J - 2) := by
    simp [Fintype.card_fun, hKcard]
  have hinner (e : E) :
      (((Finset.univ : Finset E).filter (rowConflict row e)).biUnion (fun f =>
        (Finset.univ : Finset (K → E)).image (fun t => (e, f, t)))).card ≤
      C * (Fintype.card E) ^ (J - 2) := by
    calc
      _ ≤ ((Finset.univ : Finset E).filter (rowConflict row e)).card *
          (Finset.univ : Finset (K → E)).card := by
        apply Finset.card_biUnion_le_card_mul
        intro f hf
        have hinj_t : Function.Injective (fun t : K → E => (e, f, t)) := by
          intro a b hab
          exact congrArg Prod.snd (congrArg Prod.snd hab)
        rw [Finset.card_image_of_injective _ hinj_t]
      _ ≤ C * (Fintype.card E) ^ (J - 2) := by
        rw [htailcard]
        exact Nat.mul_le_mul_right _ (hconflict e)
  have htarget : target.card ≤
      (Fintype.card E) * (C * (Fintype.card E) ^ (J - 2)) := by
    dsimp [target]
    calc
      _ ≤ (Finset.univ : Finset E).card *
          (C * (Fintype.card E) ^ (J - 2)) := by
        apply Finset.card_biUnion_le_card_mul
        intro e he
        exact hinner e
      _ = (Fintype.card E) * (C * (Fintype.card E) ^ (J - 2)) := by
        simp
  have hcard := Finset.card_le_card himage
  calc
    (pairConflictSet row i j).card =
        ((pairConflictSet row i j).image encode).card := by
      symm
      exact Finset.card_image_of_injective _ hencode
    _ ≤ target.card := hcard
    _ ≤ (Fintype.card E) * (C * (Fintype.card E) ^ (J - 2)) := htarget
    _ = C * (Fintype.card E) ^ (J - 1) := by
      have hJ : J - 1 = (J - 2) + 1 := by omega
      rw [hJ, pow_succ]
      ring

def distinctOrderedPairs (J : Nat) : Finset (Fin J × Fin J) :=
  Finset.univ.filter (fun p => p.1 ≠ p.2)

theorem distinctOrderedPairs_card (J : Nat) :
    (distinctOrderedPairs J).card = J * (J - 1) := by
  classical
  let fibers : Finset (Fin J) → Finset (Fin J × Fin J) := fun s =>
    s.biUnion (fun i => (Finset.univ.erase i).image (fun j => (i, j)))
  have hfibers :
      distinctOrderedPairs J = fibers Finset.univ := by
    ext p
    rcases p with ⟨i, j⟩
    simp [distinctOrderedPairs, fibers, Finset.mem_biUnion, ne_comm]
  have hdisj : ((Finset.univ : Finset (Fin J)) : Set (Fin J)).PairwiseDisjoint
      (fun i => (Finset.univ.erase i).image (fun j => (i, j))) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    rcases Finset.mem_image.mp hpi with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hpj with ⟨b, hb, hab⟩
    exact hij (congrArg Prod.fst hab).symm
  have hfiber_card (i : Fin J) :
      ((Finset.univ.erase i).image (fun j => (i, j))).card = J - 1 := by
    rw [Finset.card_image_of_injective _ (by
      intro a b hab
      exact congrArg Prod.snd hab)]
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
  rw [hfibers, Finset.card_biUnion hdisj]
  simp_rw [hfiber_card]
  simp [Fintype.card_fin]

theorem bad_ordered_question_count_le_of_conflict
    {X E : Type*} [Fintype X] [Fintype E]
    [DecidableEq X] [DecidableEq E]
    (row : E → Finset X) (J C : Nat)
    (hconflict : ∀ e,
      ((Finset.univ : Finset E).filter
        (rowConflict row e)).card ≤ C) :
    ((Finset.univ : Finset (Fin J → E)).filter
      (fun u => ¬ GoodOrderedQuestion row u)).card ≤
      J * (J - 1) * C * (Fintype.card E) ^ (J - 1) := by
  classical
  by_cases hJ : J < 2
  · have hgood (u : Fin J → E) : GoodOrderedQuestion row u := by
      apply not_not.mp
      intro hbad
      rcases (not_goodOrderedQuestion_iff_conflicting_pair row u).mp hbad with
        ⟨i, j, hij, _⟩
      have hij_eq : ∀ i j : Fin J, i = j := by
        intro i j
        omega
      exact hij (hij_eq i j)
    have hbad_empty :
        (Finset.univ : Finset (Fin J → E)).filter
          (fun u => ¬ GoodOrderedQuestion row u) = ∅ := by
      ext u
      simp [hgood u]
    rw [hbad_empty]
    simp
  · have hJ2 : 2 ≤ J := by omega
    let pairs : Finset (Fin J × Fin J) := distinctOrderedPairs J
    let bad : Finset (Fin J → E) :=
      Finset.univ.filter (fun u => ¬ GoodOrderedQuestion row u)
    have hbad_subset : bad ⊆ pairs.biUnion (fun p => pairConflictSet row p.1 p.2) := by
      intro u hu
      rcases (not_goodOrderedQuestion_iff_conflicting_pair row u).mp
          (Finset.mem_filter.mp hu).2 with ⟨i, j, hij, hconflict⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨(i, j), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hconflict⟩
    have hpair (p : Fin J × Fin J) (hp : p ∈ pairs) :
        (pairConflictSet row p.1 p.2).card ≤
          C * (Fintype.card E) ^ (J - 1) := by
      exact pairConflictSet_card_le row C hconflict p.1 p.2
        (Finset.mem_filter.mp hp).2
    have hcard := Finset.card_le_card hbad_subset
    dsimp [bad] at hcard
    calc
      (Finset.univ.filter (fun u => ¬ GoodOrderedQuestion row u)).card ≤
          (pairs.biUnion (fun p => pairConflictSet row p.1 p.2)).card := hcard
      _ ≤ pairs.card * (C * (Fintype.card E) ^ (J - 1)) := by
        exact Finset.card_biUnion_le_card_mul pairs
          (fun p => pairConflictSet row p.1 p.2)
          (C * (Fintype.card E) ^ (J - 1)) hpair
      _ = J * (J - 1) * C * (Fintype.card E) ^ (J - 1) := by
        rw [show pairs = distinctOrderedPairs J from rfl, distinctOrderedPairs_card]
        ring

def incidenceRows (row : E → Finset X) (x : X) : Finset E :=
  (Finset.univ : Finset E).filter (fun e => x ∈ row e)

def directConflictCandidates (row : E → Finset X) (e : E) : Finset E :=
  (row e).biUnion (incidenceRows row)

def crossConflictCandidates (row : E → Finset X) (e : E) : Finset E :=
  (row e).biUnion (fun x =>
    ((Finset.univ : Finset E).filter (fun g => x ∈ row g)).biUnion (fun g =>
      (row g).biUnion (incidenceRows row)))

theorem conflict_degree_le
    (row : E → Finset X) (D : Nat)
    (hthree : ∀ e, (row e).card = 3)
    (hdegree : ∀ x,
      ((Finset.univ : Finset E).filter
        (fun e => x ∈ row e)).card ≤ D)
    (e : E) :
    ((Finset.univ : Finset E).filter
      (rowConflict row e)).card ≤
      1 + 3 * D + 9 * D^2 := by
  classical
  have hdirect : (directConflictCandidates row e).card ≤ 3 * D := by
    calc
      (directConflictCandidates row e).card ≤ (row e).card * D := by
        exact Finset.card_biUnion_le_card_mul (row e) (incidenceRows row) D
          (fun x _ => hdegree x)
      _ = 3 * D := by rw [hthree e]
  have hy (g : E) : ((row g).biUnion (incidenceRows row)).card ≤ 3 * D := by
    calc
      ((row g).biUnion (incidenceRows row)).card ≤ (row g).card * D := by
        exact Finset.card_biUnion_le_card_mul (row g) (incidenceRows row) D
          (fun y _ => hdegree y)
      _ = 3 * D := by rw [hthree g]
  have hg (x : X) :
      (((Finset.univ : Finset E).filter (fun g => x ∈ row g)).biUnion
        (fun g => (row g).biUnion (incidenceRows row))).card ≤ 3 * D^2 := by
    calc
      _ ≤ ((Finset.univ : Finset E).filter (fun g => x ∈ row g)).card * (3 * D) := by
        exact Finset.card_biUnion_le_card_mul _ _ (3 * D)
          (fun g hg => hy g)
      _ ≤ D * (3 * D) := by
        exact Nat.mul_le_mul_right (3 * D) (hdegree x)
      _ = 3 * D^2 := by ring
  have hcross : (crossConflictCandidates row e).card ≤ 9 * D^2 := by
    calc
      (crossConflictCandidates row e).card ≤ (row e).card * (3 * D^2) := by
        exact Finset.card_biUnion_le_card_mul (row e) (fun x =>
          ((Finset.univ : Finset E).filter (fun g => x ∈ row g)).biUnion (fun g =>
            (row g).biUnion (incidenceRows row))) (3 * D^2)
          (fun x _ => hg x)
      _ = 9 * D^2 := by rw [hthree e]; ring
  have hsubset :
      ((Finset.univ : Finset E).filter (rowConflict row e)) ⊆
        (({e} : Finset E) ∪ directConflictCandidates row e) ∪
          crossConflictCandidates row e := by
    intro f hf
    rcases Finset.mem_filter.mp hf with ⟨_, hconflict⟩
    rcases hconflict with rfl | hdisj | ⟨g, x, hx, y, hyf, hxg, hyg⟩
    · simp
    · have hxy : f ∈ directConflictCandidates row e := by
        obtain ⟨z, hze, hzf⟩ := Finset.not_disjoint_iff.mp hdisj
        apply Finset.mem_biUnion.mpr
        exact ⟨z, hze, by simp [incidenceRows, hzf]⟩
      simp [hxy]
    · have hxy : f ∈ crossConflictCandidates row e := by
        apply Finset.mem_biUnion.mpr
        refine ⟨x, hx, ?_⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨g, ?_, ?_⟩
        · simp [hxg]
        · apply Finset.mem_biUnion.mpr
          exact ⟨y, hyg, by simp [incidenceRows, hyf]⟩
      simp [hxy]
  have hcard := Finset.card_le_card hsubset
  calc
    ((Finset.univ : Finset E).filter (rowConflict row e)).card ≤
        ((({e} : Finset E) ∪ directConflictCandidates row e) ∪
          crossConflictCandidates row e).card := hcard
    _ ≤ (({e} : Finset E) ∪ directConflictCandidates row e).card +
          (crossConflictCandidates row e).card := Finset.card_union_le _ _
    _ ≤ (({e} : Finset E).card + (directConflictCandidates row e).card) +
          (crossConflictCandidates row e).card := by
      gcongr
      exact Finset.card_union_le _ _
    _ ≤ 1 + 3 * D + 9 * D^2 := by
      simp only [Finset.card_singleton]
      omega

#print axioms conflict_degree_le

theorem bad_ordered_question_count_le
    {X E : Type*} [Fintype X] [Fintype E]
    [DecidableEq X] [DecidableEq E]
    (row : E → Finset X) (D J : Nat)
    (hthree : ∀ e, (row e).card = 3)
    (hdegree : ∀ x,
      ((Finset.univ : Finset E).filter
        (fun e => x ∈ row e)).card ≤ D) :
    ((Finset.univ : Finset (Fin J → E)).filter
      (fun u => ¬ GoodOrderedQuestion row u)).card ≤
      J * (J - 1) * (1 + 3 * D + 9 * D^2) *
        (Fintype.card E) ^ (J - 1) := by
  apply bad_ordered_question_count_le_of_conflict row J
    (1 + 3 * D + 9 * D^2)
  intro e
  exact conflict_degree_le row D hthree hdegree e

theorem actual_bad_ordered_question_count_le
    {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m)
    (J : Nat) :
    ((Finset.univ : Finset (Fin J → I.RowId)).filter
      (fun u => ¬ GoodOrderedQuestion I.support u)).card ≤
      J * (J - 1) * 157 * (Fintype.card I.RowId) ^ (J - 1) := by
  classical
  have h := bad_ordered_question_count_le I.support 4 J I.support_card
    (fun x => by
      have hx := rowId_incidence_card_le_four I x
      convert hx using 1
      congr 1
      letI : DecidablePred (fun q : I.RowId => x ∈ I.support q) :=
        fun q => Finset.decidableMem x (I.support q)
      have hfilter :
          @Finset.filter I.RowId (fun q : I.RowId => x ∈ I.support q)
              (fun q => Classical.propDecidable _) (Finset.univ : Finset I.RowId) =
            (Finset.univ : Finset I.RowId).filter
              (fun q : I.RowId => x ∈ I.support q) :=
        Finset.filter_congr_decidable _ _ _
      symm
      exact hfilter)
  simpa only [show (1 + 3 * 4 + 9 * 4 ^ 2 : Nat) = 157 by norm_num] using h

theorem actual_bad_ordered_question_count_mul_rowCard_le
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (J : Nat) :
    ((Finset.univ : Finset (Fin J → I.RowId)).filter
      (fun u => ¬ GoodOrderedQuestion I.support u)).card *
        Fintype.card I.RowId ≤
      (J * (J - 1) * 157) *
        Fintype.card (Fin J → I.RowId) := by
  classical
  have hcount := actual_bad_ordered_question_count_le I J
  by_cases hJ : J = 0
  · subst J
    have hzero :
        ((Finset.univ : Finset (Fin 0 → I.RowId)).filter
          (fun u => ¬ GoodOrderedQuestion I.support u)).card = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa using hcount
    rw [hzero]
    simp
  · have hJpos : 0 < J := Nat.pos_of_ne_zero hJ
    have hpow :
        (Fintype.card I.RowId) ^ (J - 1) * Fintype.card I.RowId =
          (Fintype.card I.RowId) ^ J := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hJ)]
    calc
      ((Finset.univ : Finset (Fin J → I.RowId)).filter
          (fun u => ¬ GoodOrderedQuestion I.support u)).card *
          Fintype.card I.RowId ≤
          ((J * (J - 1) * 157) *
            (Fintype.card I.RowId) ^ (J - 1)) *
            Fintype.card I.RowId :=
        Nat.mul_le_mul_right _ hcount
      _ = (J * (J - 1) * 157) *
          ((Fintype.card I.RowId) ^ (J - 1) *
            Fintype.card I.RowId) := by
        rw [Nat.mul_assoc]
      _ = (J * (J - 1) * 157) *
          (Fintype.card I.RowId) ^ J := by rw [hpow]
      _ = (J * (J - 1) * 157) *
          Fintype.card (Fin J → I.RowId) := by
        simp [Fintype.card_fun]

theorem actual_bad_ordered_question_uniform_mass_le
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (J : Nat) (hrows : 0 < Fintype.card I.RowId) :
    (((Finset.univ : Finset (Fin J → I.RowId)).filter
      (fun u => ¬ GoodOrderedQuestion I.support u)).card : ℚ) /
        (Fintype.card (Fin J → I.RowId) : ℚ) ≤
      ((J * (J - 1) * 157 : Nat) : ℚ) /
        (Fintype.card I.RowId : ℚ) := by
  have hR : (0 : ℚ) < Fintype.card I.RowId := by
    exact_mod_cast hrows
  have hT : (0 : ℚ) < Fintype.card (Fin J → I.RowId) := by
    rw [Fintype.card_fun]
    exact pow_pos hR _
  apply (div_le_div_iff₀ hT hR).2
  exact_mod_cast actual_bad_ordered_question_count_mul_rowCard_le I J

theorem ordered_good_bad_card_add_eq_total
    {X E : Type*} [Fintype X] [Fintype E]
    [DecidableEq X] [DecidableEq E]
    {J : Nat} (row : E → Finset X) :
    ((Finset.univ : Finset (Fin J → E)).filter
      (fun u => GoodOrderedQuestion row u)).card +
      ((Finset.univ : Finset (Fin J → E)).filter
        (fun u => ¬ GoodOrderedQuestion row u)).card =
      Fintype.card (Fin J → E) := by
  classical
  simpa only [Finset.card_univ] using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin J → E)))
      (p := fun u => GoodOrderedQuestion row u))

theorem actual_good_ordered_question_uniform_mass_ge
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (J : Nat) (hrows : 0 < Fintype.card I.RowId) :
    1 - ((J * (J - 1) * 157 : Nat) : ℚ) /
        (Fintype.card I.RowId : ℚ) ≤
      (((Finset.univ : Finset (Fin J → I.RowId)).filter
        (fun u => GoodOrderedQuestion I.support u)).card : ℚ) /
        (Fintype.card (Fin J → I.RowId) : ℚ) := by
  classical
  have hsum :
      (((Finset.univ : Finset (Fin J → I.RowId)).filter
        (fun u => GoodOrderedQuestion I.support u)).card : ℚ) +
          (((Finset.univ : Finset (Fin J → I.RowId)).filter
            (fun u => ¬ GoodOrderedQuestion I.support u)).card : ℚ) =
        (Fintype.card (Fin J → I.RowId) : ℚ) := by
    exact_mod_cast ordered_good_bad_card_add_eq_total I.support
  have hbad := actual_bad_ordered_question_uniform_mass_le I J hrows
  have hR : (0 : ℚ) < Fintype.card I.RowId := by
    exact_mod_cast hrows
  have hT : (0 : ℚ) < Fintype.card (Fin J → I.RowId) := by
    rw [Fintype.card_fun]
    exact pow_pos hR _
  have hgood :
      (((Finset.univ : Finset (Fin J → I.RowId)).filter
        (fun u => GoodOrderedQuestion I.support u)).card : ℚ) /
          (Fintype.card (Fin J → I.RowId) : ℚ) =
        1 - (((Finset.univ : Finset (Fin J → I.RowId)).filter
          (fun u => ¬ GoodOrderedQuestion I.support u)).card : ℚ) /
            (Fintype.card (Fin J → I.RowId) : ℚ) := by
    have hnum :
        (((Finset.univ : Finset (Fin J → I.RowId)).filter
          (fun u => GoodOrderedQuestion I.support u)).card : ℚ) =
          (Fintype.card (Fin J → I.RowId) : ℚ) -
            (((Finset.univ : Finset (Fin J → I.RowId)).filter
              (fun u => ¬ GoodOrderedQuestion I.support u)).card : ℚ) := by
      linarith [hsum]
    rw [hnum, sub_div]
    rw [div_self (ne_of_gt hT)]
  calc
    1 - ((J * (J - 1) * 157 : Nat) : ℚ) /
          (Fintype.card I.RowId : ℚ) ≤
        1 - (((Finset.univ : Finset (Fin J → I.RowId)).filter
          (fun u => ¬ GoodOrderedQuestion I.support u)).card : ℚ) /
            (Fintype.card (Fin J → I.RowId) : ℚ) :=
      sub_le_sub_left hbad 1
    _ = (((Finset.univ : Finset (Fin J → I.RowId)).filter
        (fun u => GoodOrderedQuestion I.support u)).card : ℚ) /
          (Fintype.card (Fin J → I.RowId) : ℚ) := hgood.symm

end
