/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Examples.QuadraticBowl
import LeanSharp.Theory.Dynamics.Convergence

/-!
# Example Model Tests

This module exists to sanity-check foundational properties of toy model
gradients and filtering behavior used throughout proof examples.
-/

namespace LeanSharp.Tests

open LeanSharp.QuadraticBowl

/-- Verifies the fundamental L2 contraction property of the Z-score filter on the toy model. -/
theorem test_toy_filter_contraction :
    ‖filtered_gradient (exact_gradient_toy w_init) 1‖ ≤ ‖exact_gradient_toy w_init‖ := by
  apply filtered_norm_bound

/-- Verifies that for the toy gradient, the Z-score filter (z=1) is an identity. -/
theorem test_toy_filter_identity :
    filtered_gradient (exact_gradient_toy w_init) 1 = (exact_gradient_toy w_init) := by
  exact toy_filtered_gradient_check

/-- Verifies that the toy model's gradient at the initial point is non-zero. -/
theorem test_toy_gradient_nonzero :
    exact_gradient_toy w_init ≠ 0 := by
  unfold exact_gradient_toy w_init
  intro h
  have h0 : (WithLp.equiv 2 (Fin 2 → ℝ) ((WithLp.equiv 2 (Fin 2 → ℝ)).symm fun i =>
      2 * (WithLp.equiv 2 (Fin 2 → ℝ)) ((WithLp.equiv 2 (Fin 2 → ℝ)).symm fun i =>
        if i = 0 then 1 else 3) i)) 0 = 0 := by
    rw [h]; rfl
  rw [Equiv.apply_symm_apply] at h0
  norm_num at h0

end LeanSharp.Tests
