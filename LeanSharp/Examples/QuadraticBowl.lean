/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Core.Objective
import LeanSharp.Theory.Dynamics.Convergence
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic

/-!
# Quadratic Bowl Example

This module provides a concrete demonstration of the ZSharp algorithm on a
simple 2D quadratic landscape. It verifies that the abstract definitions
in `W ι` can be explicitly evaluated on Euclidean vectors.

## Main definitions

* `toyLoss`: A simple 2D quadratic loss function $L(w_0, w_1) = w_0^2 + w_1^2$.
* `exactGradientToy`: The explicit analytical gradient of `toyLoss`.
* `wInit`: A concrete initial weight vector $[1, 3]$.

## Main theorems

* `hasFDerivAt_toyLoss`: The analytical Fréchet derivative of `toyLoss`.
* `gradient_toy_eq`: Shows that the computed gradient matches the analytical one.
-/

namespace LeanSharp.QuadraticBowl

open BigOperators

-- We work in 2D space
local notation "W2" => W (Fin 2)

/-- A simple 2D quadratic loss function $L(w_0, w_1) = w_0^2 + w_1^2$. -/
noncomputable def toyLoss (w : W2) : ℝ :=
  let w0 := (WithLp.equiv 2 (Fin 2 → ℝ) w) 0
  let w1 := (WithLp.equiv 2 (Fin 2 → ℝ) w) 1
  w0^2 + w1^2

/-- The analytical gradient of `toyLoss` is $\nabla L(w) = [2w_0, 2w_1]$. -/
noncomputable def exactGradientToy (w : W2) : W2 :=
  WithLp.equiv 2 (Fin 2 → ℝ) |>.symm fun i =>
    2 * (WithLp.equiv 2 (Fin 2 → ℝ) w) i

/-- Concrete initial weight vector: $w = [1, 3]$. -/
noncomputable def wInit : W2 :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm (fun i => if i = 0 then 1 else 3)

/-- The analytical Fréchet derivative of `toyLoss`. -/
lemma hasFDerivAt_toyLoss (w : W2) :
    HasFDerivAt toyLoss (((2 : ℝ) * w 0) • (EuclideanSpace.proj 0 : W2 →L[ℝ] ℝ) +
      ((2 : ℝ) * w 1) • (EuclideanSpace.proj 1 : W2 →L[ℝ] ℝ)) w := by
  rw [show toyLoss = fun w : W2 => (w 0) ^ 2 + (w 1) ^ 2 by ext; rfl]
  convert hasFDerivAt_quadratic 1 1 w using 1
  · ext x; simp only [one_mul]
  · ring_nf

/-- **Toy Gradient Correctness**: The computed gradient matches the analytical one
$\nabla L(w) = [2w_0, 2w_1]$. -/
theorem gradient_toy_eq (w : W2) :
    gradient toyLoss w = exactGradientToy w := by
  rw [show toyLoss = fun x : W2 => 1 * (x 0) ^ 2 + 1 * (x 1) ^ 2
      by ext x; simp only [toyLoss, WithLp.equiv_apply, one_mul]]
  rw [gradient_diagonal_quadratic_eq 1 1]
  unfold exactGradientToy
  ext i
  fin_cases i <;> norm_num [WithLp.equiv_symm_apply, WithLp.equiv_apply]

end LeanSharp.QuadraticBowl
