/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Taylor.Multilinear
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Multilinear Taylor expansion tests

 This module verifies the correctness of the multilinear Taylor bound on
 simple polynomial objectives.

 ## Main Definitions

 * `cubicObjective`: A 1D polynomial for verification.

 ## Theorems

 * `test_multilinear_taylor_cubic`: Concrete remainder bounding.
 -/

namespace LeanSharp.Tests

open Real

/-- **Cubic Test Objective**:
f(x) = (1/6) * x^3.
The 3rd derivative is constant (1), and higher derivatives are zero. -/
noncomputable def cubicObjective (x : ℝ) : ℝ := (1 / 6 : ℝ) * x ^ 3

/-- **Multilinear Taylor Bound Test**:
Verifies that for f(x) = x³/6, the difference between the actual value
and the 2nd-degree Taylor expansion is exactly bounded by the 3rd derivative. -/
theorem test_multilinear_taylor_cubic (x h : ℝ) :
    |cubicObjective (x + h) - (cubicObjective x + h * (x^2 / 2) + h^2 * (x / 2))| ≤
      (1 / 6 : ℝ) * |h|^3 := by
  -- Explicit expansion of (x + h)^3 / 6
  have h_exp : cubicObjective (x + h) =
      (1/6 : ℝ) * (x^3 + 3 * x^2 * h + 3 * x * h^2 + h^3) := by
    rw [cubicObjective]
    ring
  rw [h_exp, cubicObjective]
  ring_nf
  simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 6)]
  -- Use abs_pow to unify |h^3| and |h|^3
  rw [abs_pow]

end LeanSharp.Tests
