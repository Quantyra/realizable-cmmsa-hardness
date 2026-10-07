import PvNP.RealizableHardness.ActualManuscriptCutoffLedger
import PvNP.RealizableHardness.ActualCertifiedManuscriptParameters
import PvNP.RealizableHardness.ActualConditionalTheorem1Core

/-!
The manuscript parameter selector with all seven source cutoffs explicit.
`SourceHeightBounds` is data, not evidence that the cutoffs suffice for the
source results. In particular this module does not discharge any of them.
The plain selector theorems quantify a fixed ledger before eventual `L`.
The wrapper at the end enforces the `κ`, then integer `A`, then ledger, then
eventual `L` order. Its ledger is still external data, and no `τ`-dependent
claim is included here.
-/

namespace PvNP.RealizableHardness.ActualLedgerSelectedParameters

open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualManuscriptCutoffLedger
open PvNP.RealizableHardness.ActualCertifiedManuscriptParameters
open PvNP.RealizableHardness.ActualMZ24FixedRhoPointwiseSelector
open PvNP.RealizableHardness.ActualConditionalTheorem1Core

noncomputable def selectedM (bounds : SourceHeightBounds) (L : Nat) : Nat :=
  (selector (sourceHeightFloor bounds) L).getD 0

noncomputable def selectedSigma (bounds : SourceHeightBounds) (L : Nat) : Nat :=
  sigmaFinal L (selectedM bounds L)

noncomputable def selectedGamma (bounds : SourceHeightBounds) (L : Nat) : Rat :=
  gammaFinal (selectedM bounds L)

theorem selectedM_of_selector {bounds : SourceHeightBounds} {L m : Nat}
    (h : selector (sourceHeightFloor bounds) L = (m : WithBot Nat)) :
    selectedM bounds L = m := by
  unfold selectedM
  rw [h]
  rfl

/-- Eventual family for arbitrary previously fixed height cutoffs. The source
cutoff entries themselves remain external obligations. -/
theorem selected_parameters_eventually (bounds : SourceHeightBounds) (M : Nat) :
    ∃ L0, ∀ L, L0 ≤ L →
      ∃ m : Nat,
        selector (sourceHeightFloor bounds) L = (m : WithBot Nat) ∧
        M ≤ m ∧ Admissible (sourceHeightFloor bounds) L m ∧
        HeightLedgerReady bounds m (hBlock L m) ∧
        selectedM bounds L = m ∧
        selectedSigma bounds L = sigmaFinal L m ∧
        selectedGamma bounds L = gammaFinal m := by
  obtain ⟨L0, hL0⟩ := selected_ledger_eventually bounds M
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, hsel, hm, had, hready⟩ := hL0 L hL
  refine ⟨m, hsel, hm, had, hready, selectedM_of_selector hsel, ?_, ?_⟩
  · simp [selectedSigma, selectedM_of_selector hsel]
  · simp [selectedGamma, selectedM_of_selector hsel]

/-- The amplification inequality is uniform at every sufficiently large
selected `L`, for every fixed ledger. It does not assert that a source
inverse, decoder, or compiler applies at this height. -/
theorem selected_amplification_eventually (bounds : SourceHeightBounds) :
    ∃ L0, ∀ L, L0 ≤ L →
      (5 : Rat) ≤
        2 * (hBlock L (selectedM bounds L) : Rat) *
          (selectedM bounds L : Rat) *
          (manuscriptXi (selectedM bounds L) -
            1000 * fixedRho (selectedM bounds L)) := by
  obtain ⟨L0, hL0⟩ := selected_parameters_eventually bounds 256
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, _, hm, _, hready, hmeq, _, _⟩ := hL0 L hL
  rw [hmeq]
  exact amplification_margin_of_four_mul_m (by omega) hready.2.2.1

/-- The concrete `/16`, `/4`, `/2` block budget applies to the selected
family. Its source ledger entries are still external numerical contracts. -/
theorem selected_sigma_budget_eventually (bounds : SourceHeightBounds) :
    ∃ L0, ∀ L, L0 ≤ L →
      0 < selectedSigma bounds L ∧
      (8 * selectedSigma bounds L : Rat) =
        (gapRoot L (selectedM bounds L) : Rat) / 16 := by
  obtain ⟨L0, hL0⟩ := selected_parameters_eventually bounds 256
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, _, hm, had, _, hmeq, hseq, _⟩ := hL0 L hL
  rw [hmeq, hseq]
  have hpos : 0 < m := by omega
  have hdiv : m ∣ hBlock L m := had.2.2.2.2.2.2.1
  have h8 : 8 ≤ sigmaBase L m := had.2.2.2.2.2.2.2.2
  obtain ⟨_, hpow⟩ := sigmaFinal_two_pow hpos hdiv h8
  constructor
  · rw [hpow]
    exact Nat.two_pow_pos _
  · exact eight_sigmaFinal_rat hpos hdiv h8

/-- The manuscript gamma tends to zero for every fixed source ledger.
The requested accuracy is quantified before the eventual input length. -/
theorem selected_gamma_small_eventually (bounds : SourceHeightBounds)
    (ε : Rat) (hε : 0 < ε) :
    ∃ L0, ∀ L, L0 ≤ L → selectedGamma bounds L < ε := by
  have hε4 : (0 : Rat) < ε / 4 := div_pos hε (by norm_num)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε4
    (by norm_num : (3 / 4 : Rat) < 1)
  obtain ⟨L0, hL0⟩ := selected_parameters_eventually bounds (k * k)
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, _, hmk, _, _, hmeq, _, _⟩ := hL0 L hL
  have hq : k ≤ q m := Nat.le_sqrt.mpr hmk
  have hpow : ((3 / 4 : Rat) ^ q m) ≤ ((3 / 4 : Rat) ^ k) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hq
  have hle : 4 * ((3 / 4 : Rat) ^ q m) ≤ 4 * ((3 / 4 : Rat) ^ k) :=
    mul_le_mul_of_nonneg_left hpow (by norm_num)
  have hlt : 4 * ((3 / 4 : Rat) ^ k) < 4 * (ε / 4) :=
    mul_lt_mul_of_pos_left hk (by norm_num)
  have hcancel : (4 : Rat) * (ε / 4) = ε := by ring
  rw [selectedGamma, hmeq, gammaFinal_eq]
  exact hle.trans_lt (hlt.trans_eq hcancel)

/-- The selected cover has room for four labels, using the explicit `4m`
ledger guard rather than the old `m+2` production placeholder. -/
theorem selected_sigma_ge_four_eventually (bounds : SourceHeightBounds) :
    ∃ L0, ∀ L, L0 ≤ L → 4 ≤ selectedSigma bounds L := by
  obtain ⟨L0, hL0⟩ := selected_parameters_eventually bounds 256
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, _, hm, had, hready, hmeq, hseq, _⟩ := hL0 L hL
  rw [hseq]
  have hmpos : 0 < m := by omega
  have hdiv : m ∣ hBlock L m := had.2.2.2.2.2.2.1
  have h8 : 8 ≤ sigmaBase L m := had.2.2.2.2.2.2.2.2
  have hq : 4 ≤ hBlock L m / m := by
    apply (Nat.le_div_iff_mul_le hmpos).2
    simpa [Nat.mul_comm] using hready.2.2.1
  obtain ⟨_, hpow⟩ := sigmaFinal_two_pow hmpos hdiv h8
  rw [hpow]
  have hm1 : 255 ≤ m - 1 := by omega
  have he : 9 ≤ 2 * (hBlock L m / m) * (m - 1) := by
    have h1 : 4 * 255 ≤ (hBlock L m / m) * (m - 1) :=
      Nat.mul_le_mul hq hm1
    have h2 : 2 * (4 * 255) ≤ 2 * (hBlock L m / m) * (m - 1) := by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 h1
    exact (by decide : 9 ≤ 2 * (4 * 255)).trans h2
  have hexp : 2 ≤ 2 * (hBlock L m / m) * (m - 1) - 7 := by omega
  have hpow4 : 2 ^ 2 ≤ 2 ^ (2 * (hBlock L m / m) * (m - 1) - 7) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hexp
  simpa using hpow4

private lemma self_le_two_pow (k : Nat) : k ≤ 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    calc
      k + 1 ≤ 2 ^ k + 1 := Nat.add_le_add_right ih 1
      _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add_left (Nat.one_le_pow k 2 (by decide)) _
      _ = 2 ^ (k + 1) := by rw [← two_mul, pow_succ']

private lemma succ_le_two_pow : ∀ m, 1 ≤ m → m + 1 ≤ 2 ^ m
  | 0, h => by omega
  | 1, _ => by decide
  | m + 2, _ => by
      have ih := succ_le_two_pow (m + 1) (by omega)
      calc
        m + 2 + 1 = m + 1 + 1 + 1 := by omega
        _ ≤ 2 ^ (m + 1) + 1 := Nat.add_le_add_right ih 1
        _ ≤ 2 ^ (m + 1) + 2 ^ (m + 1) :=
          Nat.add_le_add_left (Nat.one_le_pow (m + 1) 2 (by decide)) _
        _ = 2 ^ (m + 2) := by rw [← two_mul, ← pow_succ']


/-- The selected block satisfies `log σ_L / log L → 1`: for every `k`,
the deficit `log L - log σ_L` is eventually at most `log L / k`. -/
theorem selectedSigma_log_gap (bounds : SourceHeightBounds) (k : Nat) :
    ∃ L0, ∀ L, L0 ≤ L →
      k * (log2nat L - log2nat (selectedSigma bounds L)) ≤ log2nat L := by
  by_cases hk : k = 0
  · refine ⟨0, ?_⟩
    intro L _
    simp [hk]
  obtain ⟨L0, hL0⟩ := selected_parameters_eventually bounds (max 256 (8 * k))
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, _, hmM, hAd, _, _, hσ, _⟩ := hL0 L hL
  have hm256 : 256 ≤ m := (Nat.le_max_left 256 (8 * k)).trans hmM
  have h8k : 8 * k ≤ m := (Nat.le_max_right 256 (8 * k)).trans hmM
  have hmpos : 0 < m := by omega
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  set ℓ := log2nat L
  set h := hBlock L m
  have hm_sqrt : m ≤ Nat.sqrt ℓ := hAd.2.1
  have hb_sqrt : bOf m ≤ Nat.sqrt ℓ := hAd.2.2.1
  have hdiv : m ∣ h := hAd.2.2.2.2.2.2.1
  have h8sig : 8 ≤ sigmaBase L m := hAd.2.2.2.2.2.2.2.2
  have hdenL : q m * (m + 1) < L := hAd.2.2.2.1
  obtain ⟨he7, hpow⟩ := sigmaFinal_two_pow (L := L) (m := m) hmpos hdiv h8sig
  set e := 2 * (h / m) * (m - 1)
  have hlogσ : log2nat (selectedSigma bounds L) = e - 7 := by
    rw [hσ, hpow]
    rw [log2nat, if_neg (Nat.two_pow_pos _).ne', Nat.log_pow (by decide : 1 < 2)]
  have hm_le_b : m ≤ bOf m := by
    have h1 : m ≤ 4000 * m := Nat.le_mul_of_pos_left m (by decide : 0 < 4000)
    have h2 : 4000 * m ≤ 4000 * m * m :=
      Nat.le_mul_of_pos_right (4000 * m) hmpos
    simpa [bOf, Nat.pow_two, Nat.mul_assoc] using h1.trans h2
  have hb2 : bOf m * bOf m ≤ ℓ := (Nat.le_sqrt).mp hb_sqrt
  have hm2 : m * m ≤ ℓ :=
    (Nat.mul_le_mul hm_le_b hm_le_b).trans hb2
  let D := q m * (m + 1)
  have hDpos : 0 < D := Nat.mul_pos (Nat.sqrt_pos.2 hmpos) (Nat.succ_pos m)
  have hDle : D ≤ 2 ^ (2 * m) := by
    calc
      D ≤ m * (m + 1) := Nat.mul_le_mul_right (m + 1) (Nat.sqrt_le_self m)
      _ ≤ 2 ^ m * 2 ^ m :=
        Nat.mul_le_mul (self_le_two_pow m) (succ_le_two_pow m (by omega))
      _ = 2 ^ (2 * m) := by rw [← Nat.pow_add, Nat.two_mul]
  let p1 := 2 * m + 1
  have hp1_le : p1 ≤ ℓ := by
    have h3 : 2 * m + 1 ≤ 3 * m := by omega
    have h33 : 3 * m ≤ m * m := Nat.mul_le_mul_right m (by omega : 3 ≤ m)
    exact (h3.trans h33).trans hm2
  have hLne : L ≠ 0 := by
    intro h0
    have hzero : ℓ = 0 := by simp [ℓ, log2nat, h0]
    have : (0 : Nat) < ℓ := by
      have : 0 < m * m := Nat.mul_pos hmpos hmpos
      exact this.trans_le hm2
    omega
  have hℓlog : ℓ = Nat.log 2 L := by simp [ℓ, log2nat, hLne]
  have hpowL : 2 ^ ℓ ≤ L := by
    rw [hℓlog]
    exact Nat.pow_log_le_self 2 hLne
  have hbn_eq : blockNum L m = (L - 1) / D := by
    have hmax : Nat.max D 1 = D := Nat.max_eq_left (Nat.succ_le_of_lt hDpos)
    simp [blockNum, hLne, hmax, D]
  have hbn_pow : 2 ^ (ℓ - p1) ≤ blockNum L m := by
    rw [hbn_eq]
    apply (Nat.le_div_iff_mul_le hDpos).2
    have hmul : D * 2 ^ (ℓ - p1) ≤ 2 ^ (2 * m) * 2 ^ (ℓ - p1) :=
      Nat.mul_le_mul_right _ hDle
    have hpowadd : 2 ^ (2 * m) * 2 ^ (ℓ - p1) = 2 ^ (ℓ - 1) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hhalf : 2 ^ (ℓ - 1) ≤ 2 ^ ℓ - 1 := by
      have hpos : 1 ≤ 2 ^ (ℓ - 1) := Nat.one_le_pow (ℓ - 1) 2 (by decide)
      have htwo : 2 ^ (ℓ - 1) + 2 ^ (ℓ - 1) = 2 ^ ℓ := by
        rw [← two_mul, ← pow_succ']
        congr 1
        omega
      exact Nat.le_sub_of_add_le <|
        calc
          2 ^ (ℓ - 1) + 1 ≤ 2 ^ (ℓ - 1) + 2 ^ (ℓ - 1) := Nat.add_le_add_left hpos _
          _ = 2 ^ ℓ := htwo
    have hsub : 2 ^ ℓ - 1 ≤ L - 1 := Nat.sub_le_sub_right hpowL 1
    have hcomm : 2 ^ (ℓ - p1) * D = D * 2 ^ (ℓ - p1) := Nat.mul_comm _ _
    rw [hcomm]
    exact (hmul.trans (le_of_eq hpowadd)).trans (hhalf.trans hsub)
  have hlogbn : ℓ - p1 ≤ log2nat (blockNum L m) := by
    have hne : blockNum L m ≠ 0 :=
      ne_of_gt <| lt_of_lt_of_le (Nat.two_pow_pos (ℓ - p1)) hbn_pow
    have hlog := Nat.le_log_of_pow_le (by decide : 1 < 2) hbn_pow
    simpa [log2nat, hne] using hlog
  have hℓ_bn : ℓ ≤ log2nat (blockNum L m) + p1 :=
    (Nat.sub_le_iff_le_add).mp hlogbn
  let b := bOf m
  have hbpos : 0 < 2 * b := by
    dsimp [b, bOf]
    positivity
  have hsplit := Nat.div_add_mod' (log2nat (blockNum L m)) (2 * b)
  have h2h_eq : 2 * h = log2nat (blockNum L m) / (2 * b) * (2 * b) := by
    dsimp [h, hBlock, b]
    calc
      2 * (bOf m * (log2nat (blockNum L m) / (2 * bOf m))) =
          (2 * bOf m) * (log2nat (blockNum L m) / (2 * bOf m)) := by ring
      _ = log2nat (blockNum L m) / (2 * bOf m) * (2 * bOf m) := by rw [Nat.mul_comm]
  have hrem : log2nat (blockNum L m) ≤ 2 * h + 2 * b := by
    have hr : log2nat (blockNum L m) % (2 * b) ≤ 2 * b :=
      Nat.le_of_lt (Nat.mod_lt _ hbpos)
    calc
      log2nat (blockNum L m) =
          2 * h + log2nat (blockNum L m) % (2 * b) := by
        rw [h2h_eq]
        exact hsplit.symm
      _ ≤ 2 * h + 2 * b := Nat.add_le_add_left hr _
  have h2h_log : 2 * h ≤ log2nat (blockNum L m) :=
    two_mul_hBlock_le_log2_blockNum L m
  have hlog_mono : log2nat (blockNum L m) ≤ ℓ := by
    have hbnL : blockNum L m ≤ L := by
      unfold blockNum
      split_ifs with hzero
      · exact Nat.zero_le _
      · exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
    rw [hℓlog]
    unfold log2nat
    by_cases hb0 : blockNum L m = 0
    · simp [hb0]
    · rw [if_neg hb0]
      exact Nat.log_mono_right hbnL
  have h2h_ℓ : 2 * h ≤ ℓ := h2h_log.trans hlog_mono
  have hdiv_le : 2 * (h / m) ≤ ℓ / m := by
    rw [← Nat.mul_div_assoc 2 hdiv]
    exact Nat.div_le_div_right h2h_ℓ
  have he_sub : e = 2 * h - 2 * (h / m) := by
    have hmul : (h / m) * m = h := Nat.div_mul_cancel hdiv
    have he1 : e = 2 * (h / m) * m - 2 * (h / m) := by
      dsimp [e]
      rw [Nat.mul_sub, Nat.mul_one]
    have he2 : 2 * (h / m) * m = 2 * h := by
      calc
        2 * (h / m) * m = 2 * ((h / m) * m) := by rw [Nat.mul_assoc]
        _ = 2 * h := by rw [hmul]
    rw [he1, he2]
  have he_cancel : e + 2 * (h / m) = 2 * h := by
    rw [he_sub]
    exact Nat.sub_add_cancel (Nat.mul_le_mul_left 2 (Nat.div_le_self h m))
  let p2 := 2 * b
  let p3 := ℓ / m
  let p4 : Nat := 7
  have hp1 : k * p1 ≤ ℓ / 4 := by
    have hkdiv : k ≤ m / 8 :=
      (Nat.le_div_iff_mul_le (by decide : 0 < 8)).2 (by simpa [Nat.mul_comm] using h8k)
    have h12k : 12 * k ≤ 2 * m := by
      have h1 : 12 * k ≤ 12 * (m / 8) := Nat.mul_le_mul_left 12 hkdiv
      have h2 : 12 * (m / 8) ≤ (12 * m) / 8 := by
        apply (Nat.le_div_iff_mul_le (by decide : 0 < 8)).2
        calc
          12 * (m / 8) * 8 = 12 * ((m / 8) * 8) := by rw [Nat.mul_assoc]
          _ ≤ 12 * m := Nat.mul_le_mul_left 12 (Nat.div_mul_le_self m 8)
      have h3 : (12 * m) / 8 ≤ 2 * m := by
        apply Nat.le_of_mul_le_mul_right _ (by decide : 0 < 8)
        calc
          (12 * m) / 8 * 8 ≤ 12 * m := Nat.div_mul_le_self _ _
          _ ≤ 16 * m := Nat.mul_le_mul_right m (by decide : 12 ≤ 16)
          _ = 2 * m * 8 := by ring
      exact h1.trans (h2.trans h3)
    have h12km : 12 * k * m ≤ m * m * (m * m) := by
      have hmul : 12 * k * m ≤ (2 * m) * m := Nat.mul_le_mul_right m h12k
      have h2mm : (2 * m) * m ≤ m * m * (m * m) := by
        have hm2ge : 2 ≤ m * m := by
          calc
            2 ≤ m := by omega
            _ ≤ m * m := Nat.le_mul_of_pos_right m hmpos
        calc
          (2 * m) * m = 2 * (m * m) := by rw [Nat.mul_assoc]
          _ ≤ (m * m) * (m * m) := Nat.mul_le_mul_right (m * m) hm2ge
      exact hmul.trans h2mm
    have hm4 : m * m * (m * m) ≤ ℓ := by
      have hbb : m * m ≤ bOf m := by
        simpa [bOf, Nat.pow_two] using
          Nat.le_mul_of_pos_left (m * m) (by decide : 0 < 4000)
      exact (Nat.mul_le_mul hbb hbb).trans hb2
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 4)).2
    calc
      k * p1 * 4 ≤ k * (3 * m) * 4 := by
        have h3m : p1 ≤ 3 * m := by
          dsimp [p1]
          omega
        exact Nat.mul_le_mul_right 4 (Nat.mul_le_mul_left k h3m)
      _ = 12 * k * m := by ring
      _ ≤ ℓ := h12km.trans hm4
  have hp2 : k * p2 ≤ ℓ / 4 := by
    have h8b : 8 * k ≤ b := h8k.trans hm_le_b
    have h8prod : 8 * k * b ≤ ℓ := by
      have hmul : (8 * k) * b ≤ b * b := Nat.mul_le_mul_right b h8b
      simpa [b, Nat.mul_assoc] using hmul.trans hb2
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 4)).2
    calc
      k * p2 * 4 = k * (2 * b) * 4 := by dsimp [p2]
      _ = 8 * k * b := by ring
      _ ≤ ℓ := h8prod
  have hp3 : k * p3 ≤ ℓ / 4 := by
    have hden : 0 < 8 * k := by omega
    have hquot : ℓ / m ≤ ℓ / (8 * k) := by
      apply (Nat.le_div_iff_mul_le hden).2
      calc
        (ℓ / m) * (8 * k) ≤ (ℓ / m) * m := Nat.mul_le_mul_left (ℓ / m) h8k
        _ ≤ ℓ := Nat.div_mul_le_self ℓ m
    have hmulk : k * (ℓ / m) ≤ k * (ℓ / (8 * k)) := Nat.mul_le_mul_left k hquot
    have h8 : k * (ℓ / (8 * k)) ≤ ℓ / 8 := by
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 8)).2
      calc
        k * (ℓ / (8 * k)) * 8 = (ℓ / (8 * k)) * (8 * k) := by ring
        _ ≤ ℓ := Nat.div_mul_le_self ℓ (8 * k)
    have h84 : ℓ / 8 ≤ ℓ / 4 := by
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 4)).2
      calc
        (ℓ / 8) * 4 ≤ (ℓ / 8) * 8 := Nat.mul_le_mul_left _ (by decide)
        _ ≤ ℓ := Nat.div_mul_le_self ℓ 8
    simpa [p3] using hmulk.trans (h8.trans h84)
  have hp4 : k * p4 ≤ ℓ / 4 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 4)).2
    have h64 : 64 * k * k ≤ ℓ := by
      have hmul : (8 * k) * (8 * k) ≤ m * m := Nat.mul_le_mul h8k h8k
      have hsq : (8 * k) * (8 * k) = 64 * k * k := by ring
      exact (hsq ▸ hmul).trans hm2
    calc
      k * p4 * 4 = 28 * k := by dsimp [p4]; ring
      _ ≤ 64 * k * k := by
        calc
          28 * k ≤ 64 * k := Nat.mul_le_mul_right k (by decide : 28 ≤ 64)
          _ ≤ 64 * k * k := Nat.le_mul_of_pos_right (64 * k) hkpos
      _ ≤ ℓ := h64
  have hmain : ℓ ≤ (e - 7) + (p1 + p2 + p3 + p4) := by
    have hbn_p2 : log2nat (blockNum L m) + p1 ≤ 2 * h + p2 + p1 :=
      Nat.add_le_add_right hrem p1
    have h2 : 2 * h + p2 + p1 ≤ e + 2 * (h / m) + p2 + p1 := by
      rw [← he_cancel]
    have h3 : e + 2 * (h / m) + p2 + p1 ≤ e + p3 + p2 + p1 := by
      have hle : 2 * (h / m) ≤ p3 := by simpa [p3] using hdiv_le
      exact Nat.add_le_add_right
        (Nat.add_le_add_right (Nat.add_le_add_left hle e) p2) p1
    have h4 : e + p3 + p2 + p1 ≤ (e - 7) + (p1 + p2 + p3 + p4) := by
      have h7 := Nat.sub_add_cancel he7
      dsimp [p4]
      omega
    calc
      ℓ ≤ log2nat (blockNum L m) + p1 := hℓ_bn
      _ ≤ 2 * h + p2 + p1 := hbn_p2
      _ ≤ e + 2 * (h / m) + p2 + p1 := h2
      _ ≤ e + p3 + p2 + p1 := h3
      _ ≤ (e - 7) + (p1 + p2 + p3 + p4) := h4
  have hδ : ℓ - (e - 7) ≤ p1 + p2 + p3 + p4 :=
    (Nat.sub_le_iff_le_add).mpr <| by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmain
  have hdist : k * (p1 + p2 + p3 + p4) =
      k * p1 + k * p2 + k * p3 + k * p4 := by ring
  have hquarters : k * p1 + k * p2 + k * p3 + k * p4 ≤ ℓ := by
    calc
      k * p1 + k * p2 + k * p3 + k * p4 ≤
          ℓ / 4 + ℓ / 4 + ℓ / 4 + ℓ / 4 :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hp1 hp2) hp3) hp4
      _ = 4 * (ℓ / 4) := by ring
      _ ≤ ℓ := by
        rw [Nat.mul_comm]
        exact Nat.div_mul_le_self ℓ 4
  calc
    k * (ℓ - log2nat (selectedSigma bounds L)) = k * (ℓ - (e - 7)) := by rw [hlogσ]
    _ ≤ k * (p1 + p2 + p3 + p4) := Nat.mul_le_mul_left k hδ
    _ = k * p1 + k * p2 + k * p3 + k * p4 := hdist
    _ ≤ ℓ := hquarters


theorem selected_sigma_pos_le_log (bounds : SourceHeightBounds) :
    ∃ L0, ∀ L, L0 ≤ L →
      0 < selectedSigma bounds L ∧ log2nat (selectedSigma bounds L) ≤ log2nat L := by
  obtain ⟨L0, hL0⟩ := selected_parameters_eventually bounds 256
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, _hsel, hm256, hAd, _, hm, hσ, _⟩ := hL0 L hL
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 256) hm256
  have hdiv : m ∣ hBlock L m := hAd.2.2.2.2.2.2.1
  have h8 : 8 ≤ sigmaBase L m := hAd.2.2.2.2.2.2.2.2
  obtain ⟨_he7, hpow⟩ := sigmaFinal_two_pow (L := L) (m := m) hmpos hdiv h8
  have hpos : 0 < selectedSigma bounds L := by
    rw [hσ, hpow]
    exact Nat.two_pow_pos _
  refine ⟨hpos, ?_⟩
  rw [hσ, hpow]
  have hlog : log2nat (2 ^ (2 * (hBlock L m / m) * (m - 1) - 7)) =
      2 * (hBlock L m / m) * (m - 1) - 7 := by
    rw [log2nat, if_neg (Nat.two_pow_pos _).ne', Nat.log_pow (by decide : 1 < 2)]
  rw [hlog]
  have h2h : 2 * hBlock L m ≤ log2nat (blockNum L m) :=
    two_mul_hBlock_le_log2_blockNum L m
  have hbn : blockNum L m ≤ L := by
    unfold blockNum
    split_ifs with hzero
    · exact Nat.zero_le _
    · exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hnum : log2nat (blockNum L m) ≤ log2nat L := by
    unfold log2nat
    by_cases hb0 : blockNum L m = 0
    · simp [hb0]
    · have hLz : L ≠ 0 := by
        intro hLz
        have : blockNum L m = 0 := by simp [blockNum, hLz]
        exact hb0 this
      simp [hb0, hLz, Nat.log_mono_right hbn]
  have hmul : 2 * (hBlock L m / m) * (m - 1) ≤ 2 * hBlock L m := by
    have hstep : (hBlock L m / m) * (m - 1) ≤ hBlock L m := by
      calc
        (hBlock L m / m) * (m - 1) ≤ (hBlock L m / m) * m :=
          Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ ≤ hBlock L m := Nat.div_mul_le_self _ _
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left 2 hstep
  exact ((Nat.sub_le _ 7).trans hmul).trans (h2h.trans hnum)


theorem selected_log_pos (bounds : SourceHeightBounds) :
    ∃ L0, ∀ L, L0 ≤ L → 0 < log2nat L := by
  obtain ⟨L0, hL0⟩ := selected_parameters_eventually bounds 256
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, _, hm256, hAd, _, _, _, _⟩ := hL0 L hL
  have hm : m * m ≤ log2nat L := (Nat.le_sqrt).mp hAd.2.1
  have h256 : 256 * 256 ≤ m * m := Nat.mul_le_mul hm256 hm256
  exact lt_of_lt_of_le (by decide : 0 < 256 * 256) (h256.trans hm)

/-- `log σ_L / log L` is eventually at least `1 - 1/k`. -/
theorem selectedSigma_log_ratio (bounds : SourceHeightBounds) (k : Nat) (hk : 0 < k) :
    ∃ L0, ∀ L, L0 ≤ L →
      0 < log2nat L ∧
      (1 : Rat) - (1 / (k : Rat)) ≤
        (log2nat (selectedSigma bounds L) : Rat) / (log2nat L : Rat) := by
  obtain ⟨L1, h1⟩ := selectedSigma_log_gap bounds k
  obtain ⟨L2, h2⟩ := selected_sigma_pos_le_log bounds
  obtain ⟨L3, h3⟩ := selected_log_pos bounds
  refine ⟨max L1 (max L2 L3), ?_⟩
  intro L hL
  have hL1 : L1 ≤ L := (Nat.le_max_left _ _).trans hL
  have hL2 : L2 ≤ L :=
    (Nat.le_max_left L2 L3).trans ((Nat.le_max_right L1 (max L2 L3)).trans hL)
  have hL3 : L3 ≤ L :=
    (Nat.le_max_right L2 L3).trans ((Nat.le_max_right L1 (max L2 L3)).trans hL)
  have hgap := h1 L hL1
  have hpos := h2 L hL2
  have hℓ : 0 < log2nat L := h3 L hL3
  set ℓ := log2nat L
  set s := log2nat (selectedSigma bounds L)
  have hs : s ≤ ℓ := by simpa [s, ℓ] using hpos.2
  have hδ : k * (ℓ - s) ≤ ℓ := by simpa [ℓ, s] using hgap
  have hsum : s + (ℓ - s) = ℓ := Nat.add_sub_of_le hs
  have hcast : (ℓ : Rat) = (s : Rat) + ((ℓ - s : Nat) : Rat) := by
    exact_mod_cast hsum.symm
  have hdiv : ((ℓ - s : Nat) : Rat) / (ℓ : Rat) ≤ 1 / (k : Rat) := by
    rw [div_le_div_iff₀ (by exact_mod_cast hℓ) (by exact_mod_cast hk)]
    have hmul : (ℓ - s) * k ≤ 1 * ℓ := by
      simpa [Nat.one_mul, Nat.mul_comm] using hδ
    exact_mod_cast hmul
  have hratio : (s : Rat) / (ℓ : Rat) = 1 - ((ℓ - s : Nat) : Rat) / (ℓ : Rat) := by
    have hne : (ℓ : Rat) ≠ 0 := by exact_mod_cast hℓ.ne'
    field_simp [hne]
    linarith [hcast]
  refine ⟨hℓ, ?_⟩
  calc
    (1 : Rat) - (1 / (k : Rat)) ≤
        1 - ((ℓ - s : Nat) : Rat) / (ℓ : Rat) :=
      sub_le_sub_left hdiv _
    _ = (s : Rat) / (ℓ : Rat) := hratio.symm


/-- Fix positive `κ`, choose integer `A` with `20 < κ A`, obtain the seven
fixed source cutoffs for that choice, then select blocks at every sufficiently
large input length. `boundsFor` only supplies numeric heights: it carries no
proof that a source theorem applies at those heights. There is no late `τ`
because this theorem has no `τ`-dependent conclusion. -/
theorem exists_outer_scale_and_ledger_selected_parameters
    (κ : Real) (hκ : 0 < κ)
    (boundsFor : ∀ A : Nat, 20 < κ * (A : Real) → SourceHeightBounds)
    (M : Nat) :
    ∃ A : Nat, ∃ hA : 20 < κ * (A : Real),
      ∃ L0, ∀ L, L0 ≤ L →
        ∃ m : Nat,
          selector (sourceHeightFloor (boundsFor A hA)) L = (m : WithBot Nat) ∧
          M ≤ m ∧
          Admissible (sourceHeightFloor (boundsFor A hA)) L m ∧
          HeightLedgerReady (boundsFor A hA) m (hBlock L m) ∧
          selectedM (boundsFor A hA) L = m ∧
          selectedSigma (boundsFor A hA) L = sigmaFinal L m ∧
          selectedGamma (boundsFor A hA) L = gammaFinal m := by
  obtain ⟨A, hA⟩ := exists_outer_repetition_scale κ hκ
  obtain ⟨L0, hL0⟩ := selected_parameters_eventually (boundsFor A hA) M
  exact ⟨A, hA, L0, hL0⟩

end PvNP.RealizableHardness.ActualLedgerSelectedParameters
