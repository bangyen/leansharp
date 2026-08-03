/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Tactic.ZSolve
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Z-Score Filter Algebra

These are "Green Zone" foundational proofs that do not require external assumptions.

## Theorems

* `filtered_gradient_coord_eq_mask_mul`.
* `filtered_gradient_coord_preservation`.
* `filtered_gradient_zero_of_outlier`.
* `single_outlier_extraction`.
* `z_score_mask_scale_invariance`.
-/

namespace LeanSharp

variable {ι : Type*} [Fintype ι]

open BigOperators

/-- **Coordinate decomposition for filtered gradients**: each output coordinate
equals the corresponding mask value times the original coordinate. This theorem
exists as a canonical algebraic normal form that downstream preservation/zeroing
lemmas can reuse instead of reproving coordinate formulas. -/
theorem filtered_gradient_coord_eq_mask_mul (g : W ι) (z : ℝ) (i : ι) :
    (WithLp.equiv 2 (ι → ℝ) (filteredGradient g z)) i =
      (WithLp.equiv 2 (ι → ℝ) (zScoreMask g z)) i * (WithLp.equiv 2 (ι → ℝ) g) i := by
  zsharp_solve

/-- **Coordinate Preservation**: Components that pass the Z-score filter
are preserved identically in the filtered gradient. -/
theorem filtered_gradient_coord_preservation (g : W ι) (z : ℝ) (i : ι)
    (h_mask : (WithLp.equiv 2 (ι → ℝ) (zScoreMask g z)) i = 1) :
    (WithLp.equiv 2 (ι → ℝ) (filteredGradient g z)) i =
    (WithLp.equiv 2 (ι → ℝ) g) i := by
  rw [filtered_gradient_coord_eq_mask_mul, h_mask, one_mul]

/-- **Outlier Removal**: If a component is an outlier (beyond the Z-score threshold),
it is zeroed out by the filter. -/
theorem filtered_gradient_zero_of_outlier (g : W ι) (z : ℝ) (i : ι)
    (h_outlier : z * vectorStd g < |(WithLp.equiv 2 (ι → ℝ) g) i - vectorMean g|) :
    (WithLp.equiv 2 (ι → ℝ) (filteredGradient g z)) i = 0 := by
  zsharp_solve

/-- **Outlier Removal (Idealized)**: In the case where there is exactly one outlier and
the mean is zero, the filtered gradient is the original gradient with that outlier zeroed
and every inlier preserved. -/
theorem single_outlier_extraction (g : W ι) (z : ℝ) (i : ι)
    [DecidableEq ι]
    (h_μ : vectorMean g = 0)
    (h_outlier : z * vectorStd g < |(WithLp.equiv 2 (ι → ℝ) g) i|)
    (h_others : ∀ j : ι, j ≠ i → |(WithLp.equiv 2 (ι → ℝ) g) j| ≤ z * vectorStd g) :
    filteredGradient g z = (WithLp.equiv 2 (ι → ℝ)).symm
      (fun j => if j = i then 0 else (WithLp.equiv 2 (ι → ℝ) g) j) := by
  apply (WithLp.equiv 2 (ι → ℝ)).injective
  ext j
  rw [Equiv.apply_symm_apply, WithLp.equiv_apply]
  split_ifs with hj
  · rw [hj]
    apply filtered_gradient_zero_of_outlier g z i
    rwa [h_μ, sub_zero]
  · have h_in : |(WithLp.equiv 2 (ι → ℝ) g) j - vectorMean g| ≤ z * vectorStd g := by
      rw [h_μ, sub_zero]
      exact h_others j hj
    apply filtered_gradient_coord_preservation g z j
    unfold zScoreMask
    rw [Equiv.apply_symm_apply]
    simp only [h_in, ↓reduceIte]

/-- **Scale Invariance**: The Z-score mask is invariant to global gradient scaling.
This ensures the algorithm's behavior is scale-agnostic. -/
theorem z_score_mask_scale_invariance (g : W ι) (z : ℝ) {k : ℝ} (hk : k ≠ 0) :
    zScoreMask (k • g) z = zScoreMask g z := by
  have hk_abs : 0 < |k| := abs_pos.mpr hk
  apply (WithLp.equiv 2 (ι → ℝ)).injective
  ext i
  unfold zScoreMask
  simp only [
    WithLp.equiv_apply,
    Equiv.apply_symm_apply,
    vectorMean_smul,
    vectorStd_smul
  ]
  congr! 1
  have h_pt : (k • g).ofLp i = k * g.ofLp i := rfl
  rw [h_pt, ← mul_sub, abs_mul]
  constructor <;> intro <;> nlinarith

end LeanSharp
