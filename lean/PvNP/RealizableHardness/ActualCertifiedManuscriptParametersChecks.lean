import PvNP.RealizableHardness.ActualCertifiedManuscriptParameters
import PvNP.RealizableHardness.ActualHeadlineParameters

/-!
Checks that call the manuscript parameter family. `decide` reduces the
shipped definitions; it is not `native_decide`.
-/

namespace PvNP.RealizableHardness.ActualCertifiedManuscriptParametersChecks

open PvNP.RealizableHardness.ActualCertifiedManuscriptParameters
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation

example (a cU : Nat) :
    ActualHeadlineParameters.adviceLeaf a cU = certifiedAdviceLeaf a cU := rfl

example : certifiedAdviceLeaf 100 3 = 100 - 2 * Nat.clog 2 (100 + 1) - 3 :=
  certifiedAdviceLeaf_eq 100 3

example : Nat.clog 2 101 = 7 := by decide

example : Nat.log 2 101 = 6 := by decide

/-- Ceiling advice at `a = 100`, `c_U = 3` is `100 - 2 * 7 - 3`. -/
example : certifiedAdviceLeaf 100 3 = 83 := by decide

example : certifiedAdviceLeaf 100 0 = 86 := by decide

example : gammaFinal 36 = 4 * ((3 / 4 : Rat) ^ q 36) := gammaFinal_eq 36

example : q 36 = 6 := by
  have h6 : (6 : Nat) = Nat.sqrt 36 :=
    Nat.eq_sqrt.mpr ⟨by decide, by decide⟩
  simpa [q] using h6.symm

example : gammaFinal 36 = 729 / 1024 := by
  rw [gammaFinal_eq]
  have hq : q 36 = 6 := by
    have h6 : (6 : Nat) = Nat.sqrt 36 :=
      Nat.eq_sqrt.mpr ⟨by decide, by decide⟩
    simpa [q] using h6.symm
  rw [hq]
  norm_num

example : sigmaFinal 0 1 = (sigmaBase 0 1 / 4) / 2 := sigmaFinal_eq 0 1

example : sigmaRepair 0 1 = sigmaBase 0 1 / 4 := rfl

example : sigmaBase 0 1 = gapRoot 0 1 / 16 := rfl

example (cU k : Nat) :
    ∃ a0, ∀ a, a0 ≤ a → k * (a - certifiedAdviceLeaf a cU) ≤ a :=
  (certifiedAdviceLeaf_gap cU k).imp fun _ h a ha => (h a ha).2

example (k : Nat) :
    ∃ L0, ∀ L, L0 ≤ L →
      k * (log2nat L - log2nat (certifiedSigma L)) ≤ log2nat L :=
  certifiedSigma_log_gap k

example (ε : Rat) (hε : 0 < ε) :
    ∃ L0, ∀ L, L0 ≤ L → certifiedGamma L < ε :=
  certifiedGamma_small_eventual ε hε

end PvNP.RealizableHardness.ActualCertifiedManuscriptParametersChecks
