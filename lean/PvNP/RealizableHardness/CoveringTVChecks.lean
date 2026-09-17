import PvNP.RealizableHardness.CoveringTV

/-! UNCOMPILED checks. No successful axiom audit is claimed. -/
open PvNP.RealizableHardness.CoveringTV

#print axioms blockMass_eq_mixture
#print axioms cubeSum_deletedRatio
#print axioms axis_square
#print axioms cubeSum_deletedRatio_sq
#print axioms blockMass_sum
#print axioms block_chiSquare_exact
#print axioms block_chiSquare_le
#print axioms frame_failure_le
#print axioms product_affinity
#print axioms product_hellingerSq_le
#print axioms realTV_sq_le_hellingerSq
#print axioms sqrt_deviation_sq_le
#print axioms cube_hellingerSq_le
#print axioms raw_array_tv_sq_le
#print axioms raw_array_tv_le
#print axioms binary_raw_array_tv_le
#print axioms hellingerSq_eq
#print axioms productMass_sum
#print axioms uniformCube_sum
#print axioms deletedCube_sum

example (β : ℝ) : cubeSum (blockMass (S := Fin 1) β) = 1 := blockMass_sum β
example (β : ℝ) :
    cubeSum (fun x y z : Fin 2 => (blockRatio β x y z - 1) ^ 2) / 8 =
      5 * β ^ 2 / 3 := by
  have h := block_chiSquare_exact (S := Fin 2) β
  norm_num at h
  nlinarith [h]
example : cubeSum (fun x y z : Fin 2 => (blockRatio 0 x y z - 1) ^ 2) = 0 := by
  simp [blockRatio, cubeSum]
example (β : ℝ) :
    cubeSum (fun x y z : Fin 1 => (blockRatio β x y z - 1) ^ 2) = 0 := by
  have h := block_chiSquare_exact (S := Fin 1) β
  norm_num at h
  exact h

example : 1 - (PvNP.RealizableHardness.GrassmannCounting.frameProduct 3 1 : ℚ) /
    (2 : ℚ) ^ (3 * 1) ≤ ((2 : ℚ) ^ 1 - 1) / (2 : ℚ) ^ 3 :=
  frame_failure_le 3 1 (by omega)

example (β : ℝ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    realTV (productMass (uniformCube (S := Fin 1 → ZMod 2)) 0)
      (productMass (deletedCube β) 0) ≤ 0 := by
  simpa using binary_raw_array_tv_le β hβ hβ1 0 1

example (J a : ℕ) :
    realTV (productMass (uniformCube (S := Fin a → ZMod 2)) J)
      (productMass (deletedCube 0) J) ≤ 0 := by
  simpa using binary_raw_array_tv_le 0 (by norm_num) (by norm_num) J a
