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
# Ill-Conditioned Landscape Example

This module provides a more challenging quadratic landscape with a high condition
number (gradient scales differ by an order of magnitude). This verifies that
ZSharp convergence holds even when curvature is non-uniform.

## Definitions

* `L_advanced`.
* `exact_gradient_advanced`.

## Theorems

* `hasFDerivAt_L_advanced`.
* `coordinate_dual_apply`.
* `gradient_advanced_eq`.
* `advanced_L_smooth`.
* `advanced_strongly_convex`.
-/

namespace LeanSharp.IllConditioned

open BigOperators

local notation "W2" => W (Fin 2)

/-- An ill-conditioned 2D quadratic loss function $L(w_0, w_1) = 10w_0^2 + w_1^2$. -/
noncomputable def L_advanced (w : W2) : ℝ :=
  10 * (w 0) ^ 2 + (w 1) ^ 2

/-- The analytical gradient is $\nabla L(w) = [20w_0, 2w_1]$. -/
noncomputable def exact_gradient_advanced (w : W2) : W2 :=
  WithLp.equiv 2 (Fin 2 → ℝ) |>.symm fun i =>
    if i = 0 then 20 * w 0
    else 2 * w 1

/-- The analytical Fréchet derivative of $L_{advanced}$. -/
lemma hasFDerivAt_L_advanced (w : W2) :
    HasFDerivAt L_advanced (((20 : ℝ) * w 0) • (EuclideanSpace.proj 0 : W2 →L[ℝ] ℝ) +
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
  rw [show L_advanced = fun w => 10 * (w 0) ^ 2 + (w 1) ^ 2 by ext; rfl]
  apply HasFDerivAt.add
  · convert HasFDerivAt.const_smul h0_sq (10 : ℝ) using 1
    ext; simp only [
      Fin.isValue,
      ContinuousLinearMap.coe_smul',
      Pi.smul_apply,
      PiLp.proj_apply,
      smul_eq_mul,
      p0
    ]; ring
  · convert h1_sq using 1

/-- Helper for coordinate-wise evaluation of the Riesz representative. -/
lemma coordinate_dual_apply (g : W2 →L[ℝ] ℝ) (i : Fin 2) :
    ((InnerProductSpace.toDual ℝ W2).symm g) i = g (EuclideanSpace.single i (1 : ℝ)) := by
  let v := (InnerProductSpace.toDual ℝ W2).symm g
  have hv : @inner ℝ W2 _ v (EuclideanSpace.single i (1 : ℝ)) = v i := by
    rw [EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul]
  rw [← hv, InnerProductSpace.toDual_symm_apply]

theorem gradient_advanced_eq (w : W2) :
    gradient L_advanced w = exact_gradient_advanced w := by
  let g_analytical : W2 →L[ℝ] ℝ := ((20 : ℝ) * w 0) • EuclideanSpace.proj 0 +
    ((2 : ℝ) * w 1) • EuclideanSpace.proj 1
  have hL : HasFDerivAt L_advanced g_analytical w := hasFDerivAt_L_advanced w
  unfold gradient
  rw [hL.fderiv]
  ext i
  unfold exact_gradient_advanced
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

/-- **L-Smoothness**: The gradient is Lipschitz with $L_{smooth} = 20$. -/
theorem advanced_L_smooth : is_L_smooth L_advanced 20 := by
  constructor
  · norm_num
  · intro w v
    rw [gradient_advanced_eq, gradient_advanced_eq]
    have h1 : 0 ≤ ‖exact_gradient_advanced w - exact_gradient_advanced v‖ := norm_nonneg _
    have h2 : 0 ≤ 20 * ‖w - v‖ := mul_nonneg (by norm_num) (norm_nonneg _)
    rw [← abs_of_nonneg h1, ← abs_of_nonneg h2, ← sq_le_sq]
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two,
        Fin.sum_univ_two]
    simp only [
      Fin.isValue,
      exact_gradient_advanced,
      WithLp.equiv_symm_apply,
      PiLp.sub_apply,
      ↓reduceIte,
      Real.norm_eq_abs,
      sq_abs,
      one_ne_zero
    ]
    ring_nf
    nlinarith [sq_nonneg (v 0 - w 0), sq_nonneg (v 1 - w 1)]

/-- **Strong Convexity**: The function is $\mu$-strongly convex with $\mu = 2$. -/
theorem advanced_strongly_convex : is_strongly_convex L_advanced 2 := by
  constructor
  · norm_num
  · intro w v
    simp only [
      L_advanced,
      Fin.isValue,
      inner,
      gradient_advanced_eq,
      exact_gradient_advanced,
      WithLp.equiv_symm_apply,
      PiLp.sub_apply,
      RCLike.inner_apply,
      conj_trivial,
      mul_ite,
      Fin.sum_univ_two,
      ↓reduceIte,
      one_ne_zero,
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

/-- Bundled strongly convex objective for the 2D ill-conditioned landscape. -/
noncomputable def L_advanced_bundled : StronglyConvexObjective (Fin 2) where
  toFun := L_advanced
  smoothness := 20
  differentiable := fun _ => (hasFDerivAt_L_advanced _).differentiableAt
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro w v; simpa only [dist_eq_norm] using advanced_L_smooth.2 w v
  μ := 2
  strongly_convex := advanced_strongly_convex

end LeanSharp.IllConditioned
