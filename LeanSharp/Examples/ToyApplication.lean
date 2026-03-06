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
# Toy Application of ZSharp

This module provides a concrete demonstration of the ZSharp algorithm on a
simple 2D quadratic landscape. It verifies that the abstract definitions
in `W d` can be explicitly evaluated on Euclidean vectors.

## Main definitions

* `L_toy`: A simple 2D quadratic loss function $L(w_0, w_1) = w_0^2 + w_1^2$.
* `exact_gradient_toy`: The explicit analytical gradient of `L_toy`.
* `w_init`: A concrete initial weight vector $[1, 3]$.

## Main theorems

* `exact_gradient_w_init`: Verifies the manual evaluation of the gradient at `w_init`.
-/

namespace LeanSharp.Toy

open BigOperators

-- We work in 2D space
local notation "W2" => W 2

/-- A simple 2D quadratic loss function $L(w_0, w_1) = w_0^2 + w_1^2$. -/
noncomputable def L_toy (w : W2) : ℝ :=
  let w0 := (WithLp.equiv 2 (Fin 2 → ℝ) w) 0
  let w1 := (WithLp.equiv 2 (Fin 2 → ℝ) w) 1
  w0^2 + w1^2

/-- The analytical gradient of `L_toy` is $\nabla L(w) = [2w_0, 2w_1]$. -/
noncomputable def exact_gradient_toy (w : W2) : W2 :=
  WithLp.equiv 2 (Fin 2 → ℝ) |>.symm fun i =>
    2 * (WithLp.equiv 2 (Fin 2 → ℝ) w) i

/-- Concrete initial weight vector: $w = [1, 3]$. -/
noncomputable def w_init : W2 :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm (fun i => if i = 0 then 1 else 3)

/-- **Theorem**: Evaluation of the toy exact gradient at `w_init`.
The result is $[2, 6]$. -/
theorem exact_gradient_w_init :
    exact_gradient_toy w_init =
      (WithLp.equiv 2 (Fin 2 → ℝ)).symm (fun i => if i = 0 then 2 else 6) := by
  unfold exact_gradient_toy w_init
  ext i
  simp only [Equiv.apply_symm_apply]
  fin_cases i
  · norm_num
  · norm_num

end LeanSharp.Toy
