import PvNP.RealizableHardness.MatrixGrassmannFibre

/-! Intersecting-anchor homogeneous matrix lift. -/
namespace PvNP.RealizableHardness.MatrixGrassmannIntersectingAnchor
open GrassmannCounting MatrixGrassmannMoment MatrixGrassmannFibre
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- The part of an eligible lift space lying in the sampled subspace still spans
the lift space together with the fixed anchor. -/
theorem anchor_sup_lift_inf (Q H L : Submodule (ZMod 2) V)
    (hQL : Q ≤ L) (hL : L ≤ Q ⊔ H) : Q ⊔ (L ⊓ H) = L := by
  have h := Submodule.sup_inf_assoc_of_le_of_neg_le H hQL (by simpa using hQL)
  rw [inf_comm] at h
  simpa [inf_comm] using (h.symm.trans (inf_eq_left.mpr hL))

/-- Intersecting the fixed anchor with a span of sampled columns does not
change when the anchor is first intersected with the sampled subspace. -/
theorem anchor_inf_sampled (Q H T : Submodule (ZMod 2) V) (hTH : T ≤ H) :
    Q ⊓ T = (Q ⊓ H) ⊓ T := by
  rw [inf_assoc, inf_eq_right.mpr hTH]

/-- The dimension shift from the sampled internal anchor to the full anchor
is independent of the chosen free-column span. -/
theorem finrank_anchor_sup_sampled (Q H T : Submodule (ZMod 2) V) (hTH : T ≤ H) :
    Module.finrank (ZMod 2) ↥(Q ⊔ T) + Module.finrank (ZMod 2) ↥(Q ⊓ H) =
      Module.finrank (ZMod 2) ↥Q +
        Module.finrank (ZMod 2) ↥((Q ⊓ H) ⊔ T) := by
  have h₁ := Q.finrank_sup_add_finrank_inf_eq T
  have h₂ := (Q ⊓ H).finrank_sup_add_finrank_inf_eq T
  rw [anchor_inf_sampled Q H T hTH] at h₁
  omega

theorem span_concatenate {a k : ℕ} (f : Fin a → V) (B : Fin k → V) :
    Submodule.span (ZMod 2) (Set.range (concatenate f B)) =
      Submodule.span (ZMod 2) (Set.range f) ⊔
        Submodule.span (ZMod 2) (Set.range B) := by
  rw [← Submodule.span_union]
  congr 1
  ext x
  simp [concatenate, Set.mem_range, Sum.exists]

/-- A full-rank tuple may be checked against the sampled part of its anchor.
The equivalence uses only `T ≤ H`; it does not assume `Q ≤ H`. -/
theorem independent_concatenate_iff_intersection {a z k : ℕ}
    (Q H : Submodule (ZMod 2) V)
    (f : Frame V a) (s : Frame V z)
    (hfQ : Submodule.span (ZMod 2) (Set.range f.val) = Q)
    (hsQH : Submodule.span (ZMod 2) (Set.range s.val) = Q ⊓ H)
    (B : Fin k → H) :
    LinearIndependent (ZMod 2) (concatenate f.val (fun i => (B i).val)) ↔
      LinearIndependent (ZMod 2) (concatenate s.val (fun i => (B i).val)) := by
  let T : Submodule (ZMod 2) V :=
    Submodule.span (ZMod 2) (Set.range (fun i => (B i).val))
  have hTH : T ≤ H := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact (B i).property
  have hdim := finrank_anchor_sup_sampled Q H T hTH
  have hfa : Module.finrank (ZMod 2) ↥Q = a := by
    rw [← hfQ, finrank_span_eq_card f.property]
    simp
  have hsz : Module.finrank (ZMod 2) ↥(Q ⊓ H) = z := by
    rw [← hsQH, finrank_span_eq_card s.property]
    simp
  have hspanF : Submodule.span (ZMod 2)
      (Set.range (concatenate f.val (fun i => (B i).val))) = Q ⊔ T := by
    rw [span_concatenate, hfQ]
  have hspanS : Submodule.span (ZMod 2)
      (Set.range (concatenate s.val (fun i => (B i).val))) = (Q ⊓ H) ⊔ T := by
    rw [span_concatenate, hsQH]
  rw [linearIndependent_iff_card_eq_finrank_span,
      linearIndependent_iff_card_eq_finrank_span]
  simp only [Fintype.card_sum, Fintype.card_fin]
  change (a+k = Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2)
    (Set.range (concatenate f.val (fun i => (B i).val))))) ↔
    (z+k = Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2)
      (Set.range (concatenate s.val (fun i => (B i).val)))))
  rw [hspanF, hspanS]
  rw [hfa, hsz] at hdim
  omega

/-- Span preservation for the same internalization. This is valid even for
rank-deficient tuples; rank is a separate condition above. -/
theorem span_anchor_iff_intersection (Q H L T : Submodule (ZMod 2) V)
    (hQL : Q ≤ L) (hL : L ≤ Q ⊔ H) (hTH : T ≤ H) :
    Q ⊔ T = L ↔ (Q ⊓ H) ⊔ T = L ⊓ H := by
  constructor
  · intro h
    rw [← h]
    have hm := Submodule.sup_inf_assoc_of_le_of_neg_le Q hTH (by simpa using hTH)
    simpa [sup_comm, inf_comm] using hm.symm
  · intro h
    calc
      Q ⊔ T = Q ⊔ ((Q ⊓ H) ⊔ T) := by
        simp [← sup_assoc]
      _ = Q ⊔ (L ⊓ H) := by rw [h]
      _ = L := anchor_sup_lift_inf Q H L hQL hL

/-- The sampled part of every eligible d-space has dimension z+k, where
z is the actual intersection dimension. -/
theorem finrank_lift_inf {a z k : ℕ} (Q H L : Submodule (ZMod 2) V)
    (hQ : Module.finrank (ZMod 2) ↥Q = a)
    (hS : Module.finrank (ZMod 2) ↥(Q ⊓ H) = z)
    (hLdim : Module.finrank (ZMod 2) ↥L = a+k)
    (hQL : Q ≤ L) (hL : L ≤ Q ⊔ H) :
    Module.finrank (ZMod 2) ↥(L ⊓ H) = z+k := by
  have hm := Q.finrank_sup_add_finrank_inf_eq (L ⊓ H)
  rw [anchor_sup_lift_inf Q H L hQL hL] at hm
  have hi : Q ⊓ (L ⊓ H) = Q ⊓ H := by
    rw [← inf_assoc, inf_eq_left.mpr hQL]
  rw [hi, hQ, hS, hLdim] at hm
  omega

theorem span_concatenate_iff_intersection {a z k : ℕ}
    (Q H L : Submodule (ZMod 2) V)
    (f : Frame V a) (s : Frame V z)
    (hfQ : Submodule.span (ZMod 2) (Set.range f.val) = Q)
    (hsQH : Submodule.span (ZMod 2) (Set.range s.val) = Q ⊓ H)
    (hQL : Q ≤ L) (hL : L ≤ Q ⊔ H) (B : Fin k → H) :
    Submodule.span (ZMod 2)
      (Set.range (concatenate f.val (fun i => (B i).val))) = L ↔
    Submodule.span (ZMod 2)
      (Set.range (concatenate s.val (fun i => (B i).val))) = L ⊓ H := by
  have hTH : Submodule.span (ZMod 2) (Set.range (fun i => (B i).val)) ≤ H := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact (B i).property
  rw [span_concatenate, span_concatenate, hfQ, hsQH]
  exact span_anchor_iff_intersection Q H L _ hQL hL hTH

/-- Ordered free-column tuples with image exactly L in the homogeneous
experiment. The columns are in H; the fixed frame need not be. -/
def HomFibre {a k : ℕ} (f : Frame V a) (H : Submodule (ZMod 2) V)
    (L : Grass V (a+k)) :=
  {B : Fin k → H //
    LinearIndependent (ZMod 2) (concatenate f.val (fun i => (B i).val)) ∧
      Submodule.span (ZMod 2)
        (Set.range (concatenate f.val (fun i => (B i).val))) = L.val}

instance homFibreFintype {a k : ℕ} (f : Frame V a) (H : Submodule (ZMod 2) V)
    (L : Grass V (a+k)) : Fintype (HomFibre f H L) := by
  unfold HomFibre
  infer_instance

/-- Internalize a homogeneous image fibre in L∩H. -/
def internalHomFibreEquiv {a z k : ℕ}
    (Q H : Submodule (ZMod 2) V) (L : Grass V (a+k))
    (f : Frame V a) (s : Frame V z)
    (hfQ : Submodule.span (ZMod 2) (Set.range f.val) = Q)
    (hsQH : Submodule.span (ZMod 2) (Set.range s.val) = Q ⊓ H)
    (hQL : Q ≤ L.val) (hL : L.val ≤ Q ⊔ H) :
    HomFibre f H L ≃ SpanFibre s
      ⟨L.val ⊓ H, finrank_lift_inf Q H L.val
        (by rw [← hfQ, finrank_span_eq_card f.property]; simp)
        (by rw [← hsQH, finrank_span_eq_card s.property]; simp)
        L.property hQL hL⟩ where
  toFun B := by
    let P : Grass V (z+k) := ⟨L.val ⊓ H, finrank_lift_inf Q H L.val
        (by rw [← hfQ, finrank_span_eq_card f.property]; simp)
        (by rw [← hsQH, finrank_span_eq_card s.property]; simp)
        L.property hQL hL⟩
    let b : Fin k → V := fun i => (B.val i).val
    have hr : LinearIndependent (ZMod 2) (concatenate s.val b) :=
      (independent_concatenate_iff_intersection Q H f s hfQ hsQH B.val).mp B.property.1
    have hs : Submodule.span (ZMod 2) (Set.range (concatenate s.val b)) = P.val :=
      (span_concatenate_iff_intersection Q H L.val f s hfQ hsQH hQL hL B.val).mp B.property.2
    exact ⟨⟨b, hr⟩, Subtype.ext hs⟩
  invFun B := by
    let P : Grass V (z+k) := ⟨L.val ⊓ H, finrank_lift_inf Q H L.val
        (by rw [← hfQ, finrank_span_eq_card f.property]; simp)
        (by rw [← hsQH, finrank_span_eq_card s.property]; simp)
        L.property hQL hL⟩
    let b : Fin k → H := fun i =>
      ⟨B.val.val i, (fibre_column_mem s P B i).2⟩
    have hr : LinearIndependent (ZMod 2)
        (concatenate f.val (fun i => (b i).val)) :=
      (independent_concatenate_iff_intersection Q H f s hfQ hsQH b).mpr B.val.property
    have hs : Submodule.span (ZMod 2)
        (Set.range (concatenate f.val (fun i => (b i).val))) = L.val :=
      (span_concatenate_iff_intersection Q H L.val f s hfQ hsQH hQL hL b).mpr
        (congrArg Subtype.val B.property)
    exact ⟨b, hr, hs⟩
  left_inv B := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    rfl
  right_inv B := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    rfl

/-- Every eligible image space has the same number of full-rank free-column
tuples, for an arbitrary intersection between the fixed anchor and H. -/
theorem card_homFibre {a z k : ℕ}
    (Q H : Submodule (ZMod 2) V) (L : Grass V (a+k))
    (f : Frame V a) (s : Frame V z)
    (hfQ : Submodule.span (ZMod 2) (Set.range f.val) = Q)
    (hsQH : Submodule.span (ZMod 2) (Set.range s.val) = Q ⊓ H)
    (hQL : Q ≤ L.val) (hL : L.val ≤ Q ⊔ H) :
    Fintype.card (HomFibre f H L) =
      ∏ i ∈ Finset.range k, (2^(z+k)-2^(z+i)) := by
  let P : Grass V (z+k) := ⟨L.val ⊓ H, finrank_lift_inf Q H L.val
      (by rw [← hfQ, finrank_span_eq_card f.property]; simp)
      (by rw [← hsQH, finrank_span_eq_card s.property]; simp)
      L.property hQL hL⟩
  have hsP : ∀ i, s.val i ∈ P.val := by
    intro i
    have hi : s.val i ∈ Q ⊓ H := by
      rw [← hsQH]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact ⟨hQL hi.1, hi.2⟩
  letI : Fintype (SpanFibre s P) := spanFibreFintype s P
  have he := Fintype.card_congr
    (internalHomFibreEquiv Q H L f s hfQ hsQH hQL hL)
  change Fintype.card (HomFibre f H L) = Fintype.card (SpanFibre s P) at he
  rw [he, card_spanFibre s P hsP]

/-- Full-rank homogeneous arrays sampled from H. -/
def HomRankArray {a : ℕ} (f : Frame V a) (H : Submodule (ZMod 2) V) (k : ℕ) :=
  {B : Fin k → H //
    LinearIndependent (ZMod 2) (concatenate f.val (fun i => (B i).val))}

instance homRankArrayFintype {a k : ℕ} (f : Frame V a)
    (H : Submodule (ZMod 2) V) : Fintype (HomRankArray f H k) := by
  unfold HomRankArray
  infer_instance

def homRankSpan {a k : ℕ} (f : Frame V a) (H : Submodule (ZMod 2) V)
    (B : HomRankArray f H k) : Grass V (a+k) :=
  ⟨Submodule.span (ZMod 2)
      (Set.range (concatenate f.val (fun i => (B.val i).val))), by
    simpa using finrank_span_eq_card B.property⟩

def HomEligible {a : ℕ} (f : Frame V a) (H : Submodule (ZMod 2) V)
    (k : ℕ) :=
  {L : Grass V (a+k) //
    Submodule.span (ZMod 2) (Set.range f.val) ≤ L.val ∧
      L.val ≤ Submodule.span (ZMod 2) (Set.range f.val) ⊔ H}

instance homEligibleFintype {a k : ℕ} (f : Frame V a)
    (H : Submodule (ZMod 2) V) : Fintype (HomEligible f H k) := by
  unfold HomEligible
  infer_instance

def homSpanEligible {a k : ℕ} (f : Frame V a)
    (H : Submodule (ZMod 2) V) (B : HomRankArray f H k) :
    HomEligible f H k := by
  refine ⟨homRankSpan f H B, ?_, ?_⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    cases i with
    | inl i => exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
    | inr i => exact Submodule.mem_sup_right (B.val i).property

/-- Actual full-rank homogeneous arrays disintegrate over eligible image
spaces and the already counted free-column fibres. -/
def homRankDecomposition {a k : ℕ} (f : Frame V a)
    (H : Submodule (ZMod 2) V) :
    HomRankArray f H k ≃ (L : HomEligible f H k) × HomFibre f H L.val where
  toFun B := ⟨homSpanEligible f H B, ⟨B.val, B.property, rfl⟩⟩
  invFun s := ⟨s.2.val, s.2.property.1⟩
  left_inv B := by
    apply Subtype.ext
    rfl
  right_inv s := by
    rcases s with ⟨⟨L,hL⟩,⟨B,hB,hspan⟩⟩
    have hEq : homSpanEligible f H ⟨B,hB⟩ = ⟨L,hL⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      exact hspan
    cases hEq
    rfl

/-- Homogeneous full-rank arrays induce exactly uniform mass on the
eligible Grassmann zoom, even when the anchor intersects H. -/
theorem sum_hom_rankArrays {a z k : ℕ}
    (Q H : Submodule (ZMod 2) V) (f : Frame V a) (s : Frame V z)
    (hfQ : Submodule.span (ZMod 2) (Set.range f.val) = Q)
    (hsQH : Submodule.span (ZMod 2) (Set.range s.val) = Q ⊓ H)
    (g : Grass V (a+k) → ℝ) :
    (∑ B : HomRankArray f H k, g (homRankSpan f H B)) =
      ((∏ i ∈ Finset.range k, (2^(z+k)-2^(z+i)) : ℕ) : ℝ) *
        ∑ L : HomEligible f H k, g L.val := by
  have he := (homRankDecomposition f H).sum_comp
    (fun p : (L : HomEligible f H k) × HomFibre f H L.val => g p.1.val)
  have hv (B : HomRankArray f H k) :
      g ((homRankDecomposition f H B).1.val) = g (homRankSpan f H B) := rfl
  simp only [hv] at he
  rw [he, Fintype.sum_sigma]
  have hc (L : HomEligible f H k) :
      Fintype.card (HomFibre f H L.val) =
        ∏ i ∈ Finset.range k, (2^(z+k)-2^(z+i)) :=
    card_homFibre Q H L.val f s hfQ hsQH
      (by rw [← hfQ]; exact L.property.1)
      (by rw [← hfQ]; exact L.property.2)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    hc, ← Finset.mul_sum]

/-- Deficient homogeneous matrices are assigned zero by the manuscript's
matrix lift, with no resampling or conditional-law substitution. -/
def homLiftTest {a k : ℕ} (f : Frame V a) (H : Submodule (ZMod 2) V)
    (g : Grass V (a+k) → ℝ) (B : Fin k → H) : ℝ :=
  if h : LinearIndependent (ZMod 2)
      (concatenate f.val (fun i => (B i).val)) then
    g (homRankSpan f H ⟨B,h⟩) else 0

theorem sum_homLiftTest {a k : ℕ} (f : Frame V a)
    (H : Submodule (ZMod 2) V) (g : Grass V (a+k) → ℝ) :
    (∑ B : Fin k → H, homLiftTest f H g B) =
      ∑ B : HomRankArray f H k, g (homRankSpan f H B) := by
  have hs := (Fintype.sum_subtype_add_sum_subtype
    (fun B : Fin k → H => LinearIndependent (ZMod 2)
      (concatenate f.val (fun i => (B i).val)))
    (homLiftTest f H g)).symm
  rw [hs]
  have hbad : (∑ B : {B : Fin k → H //
      ¬LinearIndependent (ZMod 2)
        (concatenate f.val (fun i => (B i).val))},
      homLiftTest f H g B.val) = 0 := by
    apply Finset.sum_eq_zero
    intro B _
    simp [homLiftTest, B.property]
  rw [hbad, add_zero]
  change (∑ B : HomRankArray f H k, homLiftTest f H g B.val) = _
  apply Finset.sum_congr rfl
  intro B _
  simp only [homLiftTest, dif_pos B.property]
  congr 1

theorem card_homRankArray {a z k : ℕ}
    (Q H : Submodule (ZMod 2) V) (f : Frame V a) (s : Frame V z)
    (hfQ : Submodule.span (ZMod 2) (Set.range f.val) = Q)
    (hsQH : Submodule.span (ZMod 2) (Set.range s.val) = Q ⊓ H) :
    Fintype.card (HomRankArray f H k) =
      (∏ i ∈ Finset.range k, (2^(z+k)-2^(z+i))) *
        Fintype.card (HomEligible f H k) := by
  have he := Fintype.card_congr (homRankDecomposition (k := k) f H)
  rw [Fintype.card_sigma] at he
  have hc (L : HomEligible f H k) :
      Fintype.card (HomFibre f H L.val) =
        ∏ i ∈ Finset.range k, (2^(z+k)-2^(z+i)) :=
    card_homFibre Q H L.val f s hfQ hsQH
      (by rw [← hfQ]; exact L.property.1)
      (by rw [← hfQ]; exact L.property.2)
  simpa only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.cast_id, mul_comm] using he

/-- Force-bearing homogeneous half of the manuscript matrix-lift density
comparison. The zoom premise is on the actual eligible interval, and the
conclusion includes every deficient matrix as a zero contribution. -/
theorem homogeneous_lift_density_le {a z k : ℕ}
    (Q H : Submodule (ZMod 2) V) (f : Frame V a) (s : Frame V z)
    (hfQ : Submodule.span (ZMod 2) (Set.range f.val) = Q)
    (hsQH : Submodule.span (ZMod 2) (Set.range s.val) = Q ⊓ H)
    (g : Grass V (a+k) → ℝ) (e : ℝ) (he : 0 ≤ e)
    (hzoom : (∑ L : HomEligible f H k, g L.val) ≤
      e * (Fintype.card (HomEligible f H k) : ℝ)) :
    (∑ B : Fin k → H, homLiftTest f H g B) ≤
      e * (Fintype.card (Fin k → H) : ℝ) := by
  rw [sum_homLiftTest, sum_hom_rankArrays Q H f s hfQ hsQH]
  let C : ℝ := ((∏ i ∈ Finset.range k,
    (2^(z+k)-2^(z+i)) : ℕ) : ℝ)
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hcard : (Fintype.card (HomRankArray f H k) : ℝ) ≤
      (Fintype.card (Fin k → H) : ℝ) := by
    exact_mod_cast Fintype.card_subtype_le
      (fun B : Fin k → H => LinearIndependent (ZMod 2)
        (concatenate f.val (fun i => (B i).val)))
  have heq : C * (Fintype.card (HomEligible f H k) : ℝ) =
      (Fintype.card (HomRankArray f H k) : ℝ) := by
    dsimp [C]
    exact_mod_cast (card_homRankArray (k := k) Q H f s hfQ hsQH).symm
  calc
    C * (∑ L : HomEligible f H k, g L.val) ≤
        C * (e * (Fintype.card (HomEligible f H k) : ℝ)) :=
      mul_le_mul_of_nonneg_left hzoom hC
    _ = e * (C * (Fintype.card (HomEligible f H k) : ℝ)) := by ring
    _ = e * (Fintype.card (HomRankArray f H k) : ℝ) := by rw [heq]
    _ ≤ e * (Fintype.card (Fin k → H) : ℝ) :=
      mul_le_mul_of_nonneg_left hcard he

/-- The constant fibre is the general linear count times one free
`Q∩H` choice for each of the k ordered columns. -/
theorem homFibre_product_eq_GL (z k : ℕ) :
    (∏ i ∈ Finset.range k, (2^(z+k)-2^(z+i))) =
      2^(z*k) * Nat.card (GL (Fin k) (ZMod 2)) := by
  calc
    (∏ i ∈ Finset.range k, (2^(z+k)-2^(z+i))) =
        ∏ i ∈ Finset.range k, (2^z * (2^k-2^i)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [pow_add, pow_add, Nat.mul_sub_left_distrib]
    _ = (2^z)^k * ∏ i ∈ Finset.range k, (2^k-2^i) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    _ = 2^(z*k) * Nat.card (GL (Fin k) (ZMod 2)) := by
      rw [← pow_mul, Matrix.card_GL_field]
      norm_num
      exact (Fin.prod_univ_eq_prod_range (fun i => 2^k-2^i) k).symm

theorem card_homFibre_GL {a z k : ℕ}
    (Q H : Submodule (ZMod 2) V) (L : Grass V (a+k))
    (f : Frame V a) (s : Frame V z)
    (hfQ : Submodule.span (ZMod 2) (Set.range f.val) = Q)
    (hsQH : Submodule.span (ZMod 2) (Set.range s.val) = Q ⊓ H)
    (hQL : Q ≤ L.val) (hL : L.val ≤ Q ⊔ H) :
    Fintype.card (HomFibre f H L) =
      2^(z*k) * Nat.card (GL (Fin k) (ZMod 2)) := by
  rw [card_homFibre Q H L f s hfQ hsQH hQL hL,
    homFibre_product_eq_GL]

end
end PvNP.RealizableHardness.MatrixGrassmannIntersectingAnchor
