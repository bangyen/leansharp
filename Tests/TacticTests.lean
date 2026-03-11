/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Tactic.ZSolve
import LeanSharp.Core.Filters
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith

namespace LeanSharp.Tests

variable {ι : Type*} [Fintype ι]

/-- Unit test for `zsharp_solve` on identity-level filtered gradient properties. -/
theorem test_zsolve_identity (g : W ι) (z : ℝ) (i : ι)
    (h_mask : (WithLp.equiv 2 (ι → ℝ) (z_score_mask g z)) i = 1) :
    (WithLp.equiv 2 (ι → ℝ) (filtered_gradient g z)) i =
    (WithLp.equiv 2 (ι → ℝ) g) i := by
  zsharp_solve

/-- Unit test for `zsharp_solve` on zero-masking behavior. -/
theorem test_zsolve_zero (g : W ι) (z : ℝ) (i : ι)
    (h_mask : (WithLp.equiv 2 (ι → ℝ) (z_score_mask g z)) i = 0) :
    (WithLp.equiv 2 (ι → ℝ) (filtered_gradient g z)) i = 0 := by
  zsharp_solve

/-- Unit test for `zsharp_solve` with explicit mean-zero outlier logic. -/
theorem test_zsolve_outlier (g : W ι) (z : ℝ) (i : ι)
    (h_μ : vector_mean g = 0)
    (h_out : |(WithLp.equiv 2 (ι → ℝ) g) i| ≥ z * vector_std g) :
    (WithLp.equiv 2 (ι → ℝ) (filtered_gradient g z)) i =
    (WithLp.equiv 2 (ι → ℝ) g) i := by
  zsharp_solve

end LeanSharp.Tests
