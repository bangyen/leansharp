/-
Copyright (c) 2024 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Z-Score Filter Algebra

This module contains lemmas regarding the algebraic properties of the Z-score filter.
These are "Green Zone" foundational proofs that do not require external axioms.
-/

namespace LeanSharp

variable {d : ℕ}

open BigOperators

/-- **Component Preservation**: If a component $i$ is within the Z-score threshold $z$,
the filtered gradient's $i$-th component is exactly the original gradient's $i$-th component. -/
theorem filtered_gradient_coord_preservation [Fact (0 < d)] (g : W d) (z : ℝ) (i : Fin d)
    (h_kept : (WithLp.equiv 2 (Fin d → ℝ) (z_score_mask g z)) i = 1) :
    (WithLp.equiv 2 (Fin d → ℝ) (filtered_gradient g z)) i =
    (WithLp.equiv 2 (Fin d → ℝ) g) i := by
  unfold filtered_gradient hadamard
  simp only [WithLp.equiv_apply, Equiv.apply_symm_apply]
  change _ * ((WithLp.equiv 2 (Fin d → ℝ) (z_score_mask g z)) i) = _
  rw [h_kept, mul_one]

/-- **Zero Outlier Amplification**: If the mean is zero, the filtered gradient
preserves all components exceeding $z \cdot \sigma$. -/
lemma outlier_preservation_zero_mean [Fact (0 < d)] (g : W d) (z : ℝ) (i : Fin d)
    (h_μ : vector_mean g = 0)
    (h_outlier : |(WithLp.equiv 2 (Fin d → ℝ) g) i| ≥ z * vector_std g) :
    (WithLp.equiv 2 (Fin d → ℝ) (filtered_gradient g z)) i =
    (WithLp.equiv 2 (Fin d → ℝ) g) i := by
  apply filtered_gradient_coord_preservation
  unfold z_score_mask
  simp only [WithLp.equiv_apply, Equiv.apply_symm_apply, h_μ]
  simp only [sub_zero]
  exact if_pos h_outlier

end LeanSharp
