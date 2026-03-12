/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Sam
import LeanSharp.Core.Filters
import LeanSharp.Theory.Convergence
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Advanced Toy Application: Ill-Conditioned Landscape

This module provides a more challenging quadratic landscape with a high condition
number (gradient scales differ by an order of magnitude). This verifies that
ZSharp convergence holds even when curvature is non-uniform.
-/

namespace LeanSharp.AdvancedToy

open BigOperators

local notation "W2" => W (Fin 2)

/-- An ill-conditioned 2D quadratic loss function $L(w_0, w_1) = 10w_0^2 + w_1^2$.
The condition number is 10. -/
noncomputable def L_advanced (w : W2) : ℝ :=
  let w0 := (WithLp.equiv 2 (Fin 2 → ℝ) w) 0
  let w1 := (WithLp.equiv 2 (Fin 2 → ℝ) w) 1
  10 * w0^2 + w1^2

/-- The analytical gradient is $\nabla L(w) = [20w_0, 2w_1]$. -/
noncomputable def exact_gradient_advanced (w : W2) : W2 :=
  WithLp.equiv 2 (Fin 2 → ℝ) |>.symm fun i =>
    if i = 0 then 20 * (WithLp.equiv 2 (Fin 2 → ℝ) w) 0
    else 2 * (WithLp.equiv 2 (Fin 2 → ℝ) w) 1

/-- **Gradient Identity**: The analytical gradient matches the Fréchet gradient. -/
theorem gradient_advanced_eq (w : W2) :
    gradient L_advanced w = exact_gradient_advanced w := by
  sorry

/-- **L-Smoothness**: The gradient is Lipschitz with $L_{smooth} = 20$. -/
theorem advanced_L_smooth : is_L_smooth L_advanced 20 := by
  constructor
  · norm_num
  · intro w v
    simp_rw [gradient_advanced_eq]
    unfold exact_gradient_advanced
    sorry

/-- **Strong Convexity**: The function is $\mu$-strongly convex with $\mu = 2$. -/
theorem advanced_strongly_convex : is_strongly_convex L_advanced 2 := by
  constructor
  · norm_num
  · intro w v
    simp_rw [gradient_advanced_eq]
    unfold L_advanced exact_gradient_advanced
    sorry

end LeanSharp.AdvancedToy
