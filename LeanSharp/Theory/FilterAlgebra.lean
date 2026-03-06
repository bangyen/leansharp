/-
Copyright (c) 2024 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Tactic.ZSolve
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Z-Score Filter Algebra

This module contains lemmas regarding the algebraic properties of the Z-score filter.
These are "Green Zone" foundational proofs that do not require external axioms.
-/

namespace LeanSharp

variable {d : ℕ}

open BigOperators

/-- **Coordinate Preservation**: Components that pass the Z-score filter
are preserved identically in the filtered gradient. -/
theorem filtered_gradient_coord_preservation [Fact (0 < d)] (g : W d) (z : ℝ) (i : Fin d)
    (h_mask : (WithLp.equiv 2 (Fin d → ℝ) (z_score_mask g z)) i = 1) :
    (WithLp.equiv 2 (Fin d → ℝ) (filtered_gradient g z)) i =
    (WithLp.equiv 2 (Fin d → ℝ) g) i := by
  zsharp_solve

/-- **Zero Outlier Amplification**: If the mean is zero, the filtered gradient
preserves all components exceeding $z \cdot \sigma$. -/
lemma outlier_preservation_zero_mean [Fact (0 < d)] (g : W d) (z : ℝ) (i : Fin d)
    (h_μ : vector_mean g = 0)
    (h_outlier : |(WithLp.equiv 2 (Fin d → ℝ) g) i| ≥ z * vector_std g) :
    (WithLp.equiv 2 (Fin d → ℝ) (filtered_gradient g z)) i =
    (WithLp.equiv 2 (Fin d → ℝ) g) i := by
  zsharp_solve

/-- **Non-Outlier Extraction**: If a component is NOT an outlier, it is zeroed out by the filter. -/
theorem filtered_gradient_zero_of_not_outlier [Fact (0 < d)] (g : W d) (z : ℝ) (i : Fin d)
    (h_not_outlier : |(WithLp.equiv 2 (Fin d → ℝ) g) i - vector_mean g| < z * vector_std g) :
    (WithLp.equiv 2 (Fin d → ℝ) (filtered_gradient g z)) i = 0 := by
  zsharp_solve

/-- **Signal-to-Noise Amplification (Idealized)**: In the case where there is exactly
one outlier and the mean is zero, the filtered gradient is exactly that outlier. -/
theorem single_outlier_extraction [Fact (1 < d)] (g : W d) (z : ℝ) (i : Fin d)
    (h_μ : vector_mean g = 0)
    (h_outlier : |(WithLp.equiv 2 (Fin d → ℝ) g) i| ≥ z * vector_std g)
    (h_others : ∀ j : Fin d, j ≠ i → |(WithLp.equiv 2 (Fin d → ℝ) g) j| < z * vector_std g) :
    filtered_gradient g z = (WithLp.equiv 2 (Fin d → ℝ)).symm
      (fun j => if j = i then (WithLp.equiv 2 (Fin d → ℝ) g) i else 0) := by
  haveI : Fact (0 < d) := ⟨by linarith [Fact.out (p := 1 < d)]⟩
  apply (WithLp.equiv 2 (Fin d → ℝ)).injective
  ext j
  simp only [Equiv.apply_symm_apply, WithLp.equiv_apply]
  split_ifs with hj
  · rw [hj]; exact outlier_preservation_zero_mean g z i h_μ h_outlier
  · have h_not := h_others j hj
    have h_μ_j : |(WithLp.equiv 2 (Fin d → ℝ) g) j - vector_mean g| < z * vector_std g := by
      rw [h_μ, sub_zero]; exact h_not
    exact filtered_gradient_zero_of_not_outlier g z j h_μ_j

/-- **Norm Reduction**: The L2 norm of the filtered gradient is always
less than or equal to the norm of the original gradient. -/
theorem filtered_norm_le [Fact (0 < d)] (g : W d) (z : ℝ) :
    ‖filtered_gradient g z‖ ≤ ‖g‖ := by
  have h_sq := filtered_gradient_norm_sq_le g z
  have h_sqrt := Real.sqrt_le_sqrt h_sq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h_sqrt
  exact h_sqrt

/-- **Sparse Signal Recovery**: In a regime where one component is much larger
than the rest (an outlier), the Z-score filter preserves it. -/
theorem sparse_signal_recovery [Fact (0 < d)] (g : W d) (z : ℝ) (i : Fin d)
    (h_sparse : |(WithLp.equiv 2 (Fin d → ℝ) g) i - vector_mean g| ≥ z * vector_std g) :
    (WithLp.equiv 2 (Fin d → ℝ) (filtered_gradient g z)) i =
    (WithLp.equiv 2 (Fin d → ℝ) g) i := by
  apply filtered_gradient_coord_preservation
  unfold z_score_mask
  simp only [WithLp.equiv_apply, Equiv.apply_symm_apply]
  split_ifs with h_cond
  · rfl
  · contradiction

end LeanSharp
