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
* `coordinate_dual_apply`: Helper for coordinate-wise evaluation of the Riesz representative.
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

/-- **Toy Perturbation**: For the quadratic bowl at $w=[1, 3]$, the perturbation
direction is aligned with the gradient $[2, 6]$. -/
noncomputable def toyPerturbation (ρ : ℝ) : W2 :=
  samPerturbation toyLoss wInit ρ

/-- The analytical Fréchet derivative of `toyLoss`. -/
lemma hasFDerivAt_toyLoss (w : W2) :
    HasFDerivAt toyLoss (((2 : ℝ) * w 0) • (EuclideanSpace.proj 0 : W2 →L[ℝ] ℝ) +
      ((2 : ℝ) * w 1) • (EuclideanSpace.proj 1 : W2 →L[ℝ] ℝ)) w := by
  let p0 : W2 →L[ℝ] ℝ := EuclideanSpace.proj 0
  let p1 : W2 →L[ℝ] ℝ := EuclideanSpace.proj 1
  have h0 : HasFDerivAt (fun x : W2 => x 0) p0 w := p0.hasFDerivAt
  have h1 : HasFDerivAt (fun x : W2 => x 1) p1 w := p1.hasFDerivAt
  have h0_sq : HasFDerivAt (fun x : W2 => (x 0) ^ 2) (((2 : ℝ) * w 0) • p0) w := by
    rw [show (fun x : W2 => (x 0) ^ 2) = (fun x => x 0 * x 0) by ext; ring]
    convert h0.mul h0 using 1
    ext; simp only [
      Fin.isValue,
      ContinuousLinearMap.coe_smul',
      Pi.smul_apply,
      PiLp.proj_apply,
      smul_eq_mul,
      ContinuousLinearMap.add_apply,
      p0
    ]; ring
  have h1_sq : HasFDerivAt (fun x : W2 => (x 1) ^ 2) (((2 : ℝ) * w 1) • p1) w := by
    rw [show (fun x : W2 => (x 1) ^ 2) = (fun x => x 1 * x 1) by ext; ring]
    convert h1.mul h1 using 1
    ext; simp only [
      Fin.isValue,
      ContinuousLinearMap.coe_smul',
      Pi.smul_apply,
      PiLp.proj_apply,
      smul_eq_mul,
      ContinuousLinearMap.add_apply,
      p1
    ]; ring
  rw [show toyLoss = fun w => (w 0) ^ 2 + (w 1) ^ 2 by ext; rfl]
  apply HasFDerivAt.add
  · convert h0_sq using 1
  · convert h1_sq using 1

/-- Helper for coordinate-wise evaluation of the Riesz representative. -/
lemma coordinate_dual_apply (g : W2 →L[ℝ] ℝ) (i : Fin 2) :
    ((InnerProductSpace.toDual ℝ W2).symm g) i = g (EuclideanSpace.single i (1 : ℝ)) := by
  let v := (InnerProductSpace.toDual ℝ W2).symm g
  have hv : @inner ℝ W2 _ v (EuclideanSpace.single i (1 : ℝ)) = v i := by
    rw [EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul]
  rw [← hv, InnerProductSpace.toDual_symm_apply]

/-- **Toy Gradient Correctness**: The computed gradient matches the analytical one
$\nabla L(w) = [2w_0, 2w_1]$. -/
theorem gradient_toy_eq (w : W2) :
    gradient toyLoss w = exactGradientToy w := by
  let g_analytical : W2 →L[ℝ] ℝ := ((2 : ℝ) * w 0) • EuclideanSpace.proj 0 +
    ((2 : ℝ) * w 1) • EuclideanSpace.proj 1
  have hL : HasFDerivAt toyLoss g_analytical w := hasFDerivAt_toyLoss w
  unfold gradient
  rw [hL.fderiv]
  ext i
  unfold exactGradientToy
  rw [coordinate_dual_apply g_analytical i]
  fin_cases i
  · simp only [
      g_analytical,
      ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,
      PiLp.proj_apply,
      smul_eq_mul,
      Fin.zero_eta
    ]
    unfold EuclideanSpace.single; rw [WithLp.equiv_symm_apply]
    norm_num
  · simp only [
      g_analytical,
      ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,
      PiLp.proj_apply,
      smul_eq_mul,
      Fin.mk_one
    ]
    unfold EuclideanSpace.single; rw [WithLp.equiv_symm_apply]
    norm_num

end LeanSharp.QuadraticBowl
