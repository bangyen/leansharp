/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Landscape
import LeanSharp.Theory.Dynamics.SecondOrder

/-!
# Second-Order Descent Tests

## Main definitions

* `quadraticBowl`: A concrete quadratic landscape for testing.

## Theorems

* `quadratic_bowl_descent_test`: Verification of the second-order descent lemma.
-/

namespace LeanSharp

open Real InnerProductSpace

/-- **Quadratic Bowl Landscape**:
f(w) = 1/2 * ‖w‖^2.
This simple objective has a constant Hessian (the identity matrix). -/
noncomputable def quadraticBowl (ι : Type*) [Fintype ι] (w : W ι) : ℝ :=
  (1 / 2 : ℝ) * ‖w‖ ^ 2

section Tests

variable {ι : Type*} [Fintype ι]

/-- **Second-Order Descent on Quadratic Bowl**:
Verifies that the descent lemma correctly predicts the objective decrease
on a quadratic objective where L_smooth = 1 and curvature κ = 1. -/
theorem quadratic_bowl_descent_test
    (w g_base g_f : W ι) (η : ℝ)
    (h_diff : Differentiable ℝ (quadraticBowl ι))
    (h_smooth : IsLSmooth (quadraticBowl ι) 1)
    (h_curv : (1 / 2 : ℝ) * ‖g_f‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖g_base‖ ^ 2) :
    quadraticBowl ι (w - η • g_f) ≤
      quadraticBowl ι w - η * inner ℝ (gradient (quadraticBowl ι) w) g_f +
        (η^2 / 2) * ‖g_base‖ ^ 2 := by
  -- We instantiate the general lemma with L_smooth = 1 and κ = 1.
  -- The curvature hypothesis matches the lemma's requirement.
  simpa only [mul_one] using (
    zsharp_second_order_descent
      (quadraticBowl ι) w g_base g_f η 1 1 h_diff h_smooth h_curv
  )

end Tests

end LeanSharp
