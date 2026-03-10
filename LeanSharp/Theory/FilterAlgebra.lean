/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Tactic.ZSolve
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Field.Basic

/-!
# Z-Score Filter Algebra

These are "Green Zone" foundational proofs that do not require external axioms.
-/

namespace LeanSharp

variable {d : ℕ}

open BigOperators

/-- **Coordinate Preservation**: Components that pass the Z-score filter
are preserved identically in the filtered gradient. -/
theorem filtered_gradient_coord_preservation (g : W d) (z : ℝ) (i : Fin d)
    (h_mask : (WithLp.equiv 2 (Fin d → ℝ) (z_score_mask g z)) i = 1) :
    (WithLp.equiv 2 (Fin d → ℝ) (filtered_gradient g z)) i =
    (WithLp.equiv 2 (Fin d → ℝ) g) i := by
  zsharp_solve

/-- **Non-Outlier Extraction**: If a component is NOT an outlier, it is zeroed out by the filter. -/
theorem filtered_gradient_zero_of_not_outlier (g : W d) (z : ℝ) (i : Fin d)
    (h_not_outlier : |(WithLp.equiv 2 (Fin d → ℝ) g) i - vector_mean g| < z * vector_std g) :
    (WithLp.equiv 2 (Fin d → ℝ) (filtered_gradient g z)) i = 0 := by
  zsharp_solve

/-- **Signal-to-Noise Amplification (Idealized)**: In the case where there is exactly
one outlier and the mean is zero, the filtered gradient is exactly that outlier. -/
theorem single_outlier_extraction (g : W d) (z : ℝ) (i : Fin d)
    (h_μ : vector_mean g = 0)
    (h_outlier : |(WithLp.equiv 2 (Fin d → ℝ) g) i| ≥ z * vector_std g)
    (h_others : ∀ j : Fin d, j ≠ i → |(WithLp.equiv 2 (Fin d → ℝ) g) j| < z * vector_std g) :
    filtered_gradient g z = (WithLp.equiv 2 (Fin d → ℝ)).symm
      (fun j => if j = i then (WithLp.equiv 2 (Fin d → ℝ) g) i else 0) := by
  apply (WithLp.equiv 2 (Fin d → ℝ)).injective
  ext j
  simp only [Equiv.apply_symm_apply, WithLp.equiv_apply]
  split_ifs with hj
  · rw [hj]; zsharp_solve
  · have h_not := h_others j hj
    have h_μ_j : |(WithLp.equiv 2 (Fin d → ℝ) g) j - vector_mean g| < z * vector_std g := by
      rw [h_μ, sub_zero]; exact h_not
    exact filtered_gradient_zero_of_not_outlier g z j h_μ_j


/-- **Sparse Signal Recovery**: In a regime where one component is much larger
than the rest (an outlier), the Z-score filter preserves it. -/
theorem sparse_signal_recovery (g : W d) (z : ℝ) (i : Fin d)
    (h_sparse : |(WithLp.equiv 2 (Fin d → ℝ) g) i - vector_mean g| ≥ z * vector_std g) :
    (WithLp.equiv 2 (Fin d → ℝ) (filtered_gradient g z)) i =
    (WithLp.equiv 2 (Fin d → ℝ) g) i := by
  apply filtered_gradient_coord_preservation
  simpa [z_score_mask] using h_sparse

/-- **Scale Invariance**: The Z-score mask is invariant to global gradient scaling.
This ensures the algorithm's behavior is scale-agnostic. -/
theorem z_score_mask_scale_invariance (g : W d) (z : ℝ) {k : ℝ} (hk : 0 < k) :
    z_score_mask (k • g) z = z_score_mask g z := by
  apply (WithLp.equiv 2 (Fin d → ℝ)).injective
  ext i
  unfold z_score_mask
  simp only [WithLp.equiv_apply, Equiv.apply_symm_apply, vector_mean_smul, vector_std_smul hk.le]
  congr! 1
  have h_pt : (k • g).ofLp i = k * g.ofLp i := rfl
  rw [h_pt, ← mul_sub, abs_mul, abs_of_pos hk, mul_left_comm]
  constructor <;> intro <;> nlinarith

end LeanSharp
