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
* `filtered_gradient_zero_of_not_outlier`.
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
    (WithLp.equiv 2 (ι → ℝ) (filtered_gradient g z)) i =
      (WithLp.equiv 2 (ι → ℝ) (z_score_mask g z)) i * (WithLp.equiv 2 (ι → ℝ) g) i := by
  zsharp_solve

/-- **Coordinate Preservation**: Components that pass the Z-score filter
are preserved identically in the filtered gradient. -/
theorem filtered_gradient_coord_preservation (g : W ι) (z : ℝ) (i : ι)
    (h_mask : (WithLp.equiv 2 (ι → ℝ) (z_score_mask g z)) i = 1) :
    (WithLp.equiv 2 (ι → ℝ) (filtered_gradient g z)) i =
    (WithLp.equiv 2 (ι → ℝ) g) i := by
  rw [filtered_gradient_coord_eq_mask_mul, h_mask, one_mul]

/-- **Non-Outlier Extraction**: If a component is NOT an outlier, it is zeroed out by the filter. -/
theorem filtered_gradient_zero_of_not_outlier (g : W ι) (z : ℝ) (i : ι)
    (h_not_outlier : |(WithLp.equiv 2 (ι → ℝ) g) i - vector_mean g| < z * vector_std g) :
    (WithLp.equiv 2 (ι → ℝ) (filtered_gradient g z)) i = 0 := by
  zsharp_solve

/-- **Signal-to-Noise Amplification (Idealized)**: In the case where there is exactly
one outlier and the mean is zero, the filtered gradient is exactly that outlier. -/
theorem single_outlier_extraction (g : W ι) (z : ℝ) (i : ι)
    [DecidableEq ι]
    (h_μ : vector_mean g = 0)
    (h_outlier : |(WithLp.equiv 2 (ι → ℝ) g) i| ≥ z * vector_std g)
    (h_others : ∀ j : ι, j ≠ i → |(WithLp.equiv 2 (ι → ℝ) g) j| < z * vector_std g) :
    filtered_gradient g z = (WithLp.equiv 2 (ι → ℝ)).symm
      (fun j => if j = i then (WithLp.equiv 2 (ι → ℝ) g) i else 0) := by
  apply (WithLp.equiv 2 (ι → ℝ)).injective
  ext j
  rw [
    Equiv.apply_symm_apply,
    WithLp.equiv_apply
  ]
  split_ifs with hj
  · rw [hj]; zsharp_solve
  · have h_not := h_others j hj
    have h_μ_j : |(WithLp.equiv 2 (ι → ℝ) g) j - vector_mean g| < z * vector_std g := by
      rw [h_μ, sub_zero]; exact h_not
    exact filtered_gradient_zero_of_not_outlier g z j h_μ_j

/-- **Scale Invariance**: The Z-score mask is invariant to global gradient scaling.
This ensures the algorithm's behavior is scale-agnostic. -/
theorem z_score_mask_scale_invariance (g : W ι) (z : ℝ) {k : ℝ} (hk : k ≠ 0) :
    z_score_mask (k • g) z = z_score_mask g z := by
  have hk_abs : 0 < |k| := abs_pos.mpr hk
  apply (WithLp.equiv 2 (ι → ℝ)).injective
  ext i
  unfold z_score_mask
  simp only [
    WithLp.equiv_apply,
    Equiv.apply_symm_apply,
    vector_mean_smul,
    vector_std_smul
  ]
  congr! 1
  have h_pt : (k • g).ofLp i = k * g.ofLp i := rfl
  rw [h_pt, ← mul_sub, abs_mul]
  constructor <;> intro <;> nlinarith

end LeanSharp
