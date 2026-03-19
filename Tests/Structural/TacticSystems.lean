/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Core.Filters
import LeanSharp.Tactic.ZSolve
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith

/-!
# Tactic Tests

This module exists to exercise `zsharp_solve` on representative goals, ensuring
proof automation remains stable as core lemmas evolve.

## Examples

* `test_zsolve_identity`.
* `test_zsolve_zero`.
* `test_zsolve_outlier`.
-/

namespace LeanSharp.Tests

variable {ι : Type*} [Fintype ι]

/-- Unit test for `zsharp_solve` on identity-level filtered gradient properties. -/
example (g : W ι) (z : ℝ) (i : ι)
    (h_mask : (WithLp.equiv 2 (ι → ℝ) (zScoreMask g z)) i = 1) :
    (WithLp.equiv 2 (ι → ℝ) (filteredGradient g z)) i =
    (WithLp.equiv 2 (ι → ℝ) g) i := by
  zsharp_solve

/-- Unit test for `zsharp_solve` on zero-masking behavior. -/
example (g : W ι) (z : ℝ) (i : ι)
    (h_mask : (WithLp.equiv 2 (ι → ℝ) (zScoreMask g z)) i = 0) :
    (WithLp.equiv 2 (ι → ℝ) (filteredGradient g z)) i = 0 := by
  zsharp_solve

/-- Unit test for `zsharp_solve` with explicit mean-zero outlier logic. -/
example (g : W ι) (z : ℝ) (i : ι)
    (h_μ : vectorMean g = 0)
    (h_out : |(WithLp.equiv 2 (ι → ℝ) g) i| ≥ z * vectorStd g) :
    (WithLp.equiv 2 (ι → ℝ) (filteredGradient g z)) i =
    (WithLp.equiv 2 (ι → ℝ) g) i := by
  zsharp_solve

end LeanSharp.Tests
