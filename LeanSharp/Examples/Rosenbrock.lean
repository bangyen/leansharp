/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Landscape
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Rosenbrock Example

This module implements the 2D Rosenbrock function and its analytical gradient.
$L(x, y) = (1 - x)^2 + 100(y - x^2)^2$.
-/

namespace LeanSharp.Rosenbrock

open BigOperators

local notation "W2" => W (Fin 2)

/-- The 2D Rosenbrock function: $L(x, y) = (1 - x)^2 + 100(y - x^2)^2$. -/
noncomputable def L_rosenbrock (w : W2) : ℝ :=
  (1 - w 0)^2 + 100 * (w 1 - (w 0)^2)^2

/-- The analytical gradient of $L_{rosenbrock}$. -/
noncomputable def exact_gradient_rosenbrock (w : W2) : W2 :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm fun i =>
    if i = 0 then
      -2 * (1 - w 0) - 400 * w 0 * (w 1 - (w 0)^2)
    else
      200 * (w 1 - (w 0)^2)

/-- Verification that the Rosenbrock function can be evaluated. -/
noncomputable example (w : W2) : ℝ := L_rosenbrock w

/-- Verification that the analytical gradient can be evaluated. -/
noncomputable example (w : W2) : W2 := exact_gradient_rosenbrock w

end LeanSharp.Rosenbrock
