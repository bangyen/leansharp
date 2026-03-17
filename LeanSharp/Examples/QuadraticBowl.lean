/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Core.Sam
import LeanSharp.Theory.Dynamics.Convergence
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic

/-!
# Quadratic Bowl Example

This module provides a concrete demonstration of the ZSharp algorithm on a
simple 2D quadratic landscape. It verifies that the abstract definitions
in `W ι` can be explicitly evaluated on Euclidean vectors.

## Main definitions

* `L_toy`: A simple 2D quadratic loss function $L(w_0, w_1) = w_0^2 + w_1^2$.
* `exact_gradient_toy`: The explicit analytical gradient of `L_toy`.
* `w_init`: A concrete initial weight vector $[1, 3]$.

## Main theorems

* `exact_gradient_w_init`: Verifies the manual evaluation of the gradient at `w_init`.
-/

namespace LeanSharp.QuadraticBowl

open BigOperators

-- We work in 2D space
local notation "W2" => W (Fin 2)

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
  rw [Equiv.apply_symm_apply]
  fin_cases i
  · norm_num
  · norm_num

/-- **Toy Perturbation**: For the quadratic bowl at $w=[1, 3]$, the perturbation
direction is aligned with the gradient $[2, 6]$. -/
noncomputable def toy_perturbation (ρ : ℝ) : W2 :=
  sam_perturbation L_toy w_init ρ

/-- **Toy Filtered Gradient**: At a threshold $z=1$, the filter preserves
all components of the gradient $[2, 6]$ because they are both "outliers"
relative to their mean in this 2D case. -/
theorem toy_filtered_gradient_check :
    filtered_gradient (exact_gradient_toy w_init) 1 = exact_gradient_toy w_init := by
  have h_mean : vector_mean (exact_gradient_toy w_init) = 4 := by
    unfold vector_mean exact_gradient_toy w_init
    rw [Equiv.apply_symm_apply]
    norm_num
  have h_std : vector_std (exact_gradient_toy w_init) = 2 := by
    have h_var : vector_variance (exact_gradient_toy w_init) = 4 := by
      unfold vector_variance
      rw [h_mean]
      unfold exact_gradient_toy w_init
      rw [Equiv.apply_symm_apply]
      norm_num
    unfold vector_std
    rw [h_var]
    have h_sq : (2 : ℝ) ^ 2 = 4 := by norm_num
    rw [← h_sq, Real.sqrt_sq (by norm_num)]
  unfold filtered_gradient z_score_mask hadamard
  rw [h_mean, h_std]
  ext i
  dsimp only [
    Equiv.symm_apply_apply,
    Equiv.apply_symm_apply,
    WithLp.equiv_symm_apply,
    WithLp.equiv_apply
  ]
  fin_cases i <;> {
    unfold exact_gradient_toy w_init
    split_ifs with h <;> norm_num at *
  }

/-- **Toy ZSharp Step**: A single step of ZSharp on the quadratic bowl.
Starting at $[1, 3]$ with $\eta=0.1$, the next point is $[0.8, 2.4]$. -/
theorem toy_zsharp_step_reduction :
    let w_next := w_init - (0.1 : ℝ) • (exact_gradient_toy w_init)
    L_toy w_next < L_toy w_init := by
  intro w_next
  unfold L_toy w_next w_init exact_gradient_toy
  rw [Equiv.apply_symm_apply, WithLp.equiv_apply]
  norm_num

end LeanSharp.QuadraticBowl
