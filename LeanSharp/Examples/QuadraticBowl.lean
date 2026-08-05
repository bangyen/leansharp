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
import Mathlib.Tactic.Linarith

/-!
# Quadratic Bowl Example

This module provides a concrete demonstration of the ZSharp algorithm on a
simple 2D quadratic landscape. It verifies that the abstract definitions
in `W ι` can be explicitly evaluated on Euclidean vectors.

## Main definitions

* `toyLoss`: A simple 2D quadratic loss function $L(w_0, w_1) = w_0^2 + w_1^2$.
* `exactGradientToy`: The explicit analytical gradient of `toyLoss`.
* `wInit`: A concrete initial weight vector $[1, 3]$.
* `toyLossBundled`: The bundled strongly convex objective for the quadratic bowl.

## Main theorems

* `hasFDerivAt_toyLoss`: The analytical Fréchet derivative of `toyLoss`.
* `gradient_toy_eq`: Shows that the computed gradient matches the analytical one.
* `toy_L_smooth`: The gradient is Lipschitz with $L = 2$.
* `toy_strongly_convex`: The function is $\mu$-strongly convex with $\mu = 2$.
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

/-- **L-Smoothness**: The gradient is Lipschitz with $L_{smooth} = 2$. -/
theorem toy_L_smooth : IsLSmooth toyLoss 2 := by
  constructor
  · norm_num
  · intro w v
    rw [gradient_toy_eq, gradient_toy_eq]
    have h1 : 0 ≤ ‖exactGradientToy w - exactGradientToy v‖ := norm_nonneg _
    have h2 : 0 ≤ 2 * ‖w - v‖ := mul_nonneg (by norm_num) (norm_nonneg _)
    rw [← abs_of_nonneg h1, ← abs_of_nonneg h2, ← sq_le_sq]
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two,
        Fin.sum_univ_two]
    simp only [
      Fin.isValue,
      exactGradientToy,
      WithLp.equiv_symm_apply,
      WithLp.equiv_apply,
      PiLp.sub_apply,
      Real.norm_eq_abs,
      sq_abs
    ]
    ring_nf
    nlinarith [sq_nonneg (v 0 - w 0), sq_nonneg (v 1 - w 1)]

/-- **Strong Convexity**: The function is $\mu$-strongly convex with $\mu = 2$. -/
theorem toy_strongly_convex : IsStronglyConvex toyLoss 2 := by
  constructor
  · norm_num
  · intro w v
    simp only [
      toyLoss,
      Fin.isValue,
      inner,
      gradient_toy_eq,
      exactGradientToy,
      WithLp.equiv_symm_apply,
      WithLp.equiv_apply,
      PiLp.sub_apply,
      RCLike.inner_apply,
      conj_trivial,
      Fin.sum_univ_two,
      ne_eq,
      OfNat.ofNat_ne_zero,
      not_false_eq_true,
      div_self,
      EuclideanSpace.norm_sq_eq,
      Real.norm_eq_abs,
      sq_abs,
      one_mul,
      ge_iff_le
    ]
    ring_nf
    nlinarith [sq_nonneg (v 0 - w 0), sq_nonneg (v 1 - w 1)]

/-- Bundled strongly convex objective for the 2D quadratic bowl. -/
noncomputable def toyLossBundled : StronglyConvexObjective (Fin 2) where
  toFun := toyLoss
  smoothness := 2
  differentiable := fun _ => (hasFDerivAt_toyLoss _).differentiableAt
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro w v; simpa only [dist_eq_norm] using toy_L_smooth.2 w v
  μ := 2
  strongly_convex := toy_strongly_convex

end LeanSharp.QuadraticBowl
