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

/-! An ill-conditioned 2D quadratic loss function $L(w_0, w_1) = 10w_0^2 + w_1^2$.
The condition number is 10. -/
noncomputable def L_advanced (w : W2) : ℝ :=
  10 * (w 0) ^ 2 + (w 1) ^ 2

/-- The analytical gradient is $\nabla L(w) = [20w_0, 2w_1]$. -/
noncomputable def exact_gradient_advanced (w : W2) : W2 :=
  WithLp.equiv 2 (Fin 2 → ℝ) |>.symm fun i =>
    if i = 0 then 20 * w 0
    else 2 * w 1


/-- The analytical Fréchet derivative of $L_{advanced}$. -/
lemma hasFDerivAt_L_advanced (w : W2) :
    HasFDerivAt L_advanced (((20 : ℝ) * w 0) • (EuclideanSpace.proj 0 : W2 →L[ℝ] ℝ) + ((2 : ℝ) * w 1) • (EuclideanSpace.proj 1 : W2 →L[ℝ] ℝ)) w := by
  let p0 : W2 →L[ℝ] ℝ := EuclideanSpace.proj 0
  let p1 : W2 →L[ℝ] ℝ := EuclideanSpace.proj 1
  have h0 : HasFDerivAt (fun x : W2 => x 0) p0 w := p0.hasFDerivAt
  have h1 : HasFDerivAt (fun x : W2 => x 1) p1 w := p1.hasFDerivAt
  have h0_sq : HasFDerivAt (fun x : W2 => (x 0) ^ 2) (((2 : ℝ) * w 0) • p0) w := by
    rw [show (fun x : W2 => (x 0) ^ 2) = (fun x => x 0 * x 0) by ext; ring]
    convert h0.mul h0 using 1
    ext; simp [p0, smul_eq_mul]; ring
  have h1_sq : HasFDerivAt (fun x : W2 => (x 1) ^ 2) (((2 : ℝ) * w 1) • p1) w := by
    rw [show (fun x : W2 => (x 1) ^ 2) = (fun x => x 1 * x 1) by ext; ring]
    convert h1.mul h1 using 1
    ext; simp [p1, smul_eq_mul]; ring
  rw [show L_advanced = fun w => 10 * (w 0) ^ 2 + (w 1) ^ 2 by ext; rfl]
  apply HasFDerivAt.add
  · convert HasFDerivAt.const_smul h0_sq (10 : ℝ) using 1
    ext; simp [p0, smul_eq_mul]; ring
  · convert h1_sq using 1

/-- Helper for coordinate-wise evaluation of the Riesz representative. -/
lemma coordinate_dual_apply (g : W2 →L[ℝ] ℝ) (i : Fin 2) :
    ((InnerProductSpace.toDual ℝ W2).symm g) i = g (EuclideanSpace.single i (1 : ℝ)) := by
  let v := (InnerProductSpace.toDual ℝ W2).symm g
  have hv : @inner ℝ W2 _ v (EuclideanSpace.single i (1 : ℝ)) = v i := by
    simp only [EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul]
  rw [← hv, InnerProductSpace.toDual_symm_apply]

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

theorem gradient_advanced_eq (w : W2) :
    gradient L_advanced w = exact_gradient_advanced w := by
  let g_analytical : W2 →L[ℝ] ℝ := ((20 : ℝ) * w 0) • EuclideanSpace.proj 0 + ((2 : ℝ) * w 1) • EuclideanSpace.proj 1
  have hL : HasFDerivAt L_advanced g_analytical w := hasFDerivAt_L_advanced w
  unfold gradient
  rw [hL.fderiv]
  ext i
  unfold exact_gradient_advanced
  rw [coordinate_dual_apply g_analytical i]
  fin_cases i
  · simp (config := {zeta := true}) only [g_analytical, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, PiLp.proj_apply, Pi.single_apply, mul_one, mul_zero,
      add_zero, smul_eq_mul, ite_true, ite_false, Fin.zero_eta]
    unfold EuclideanSpace.single; simp only [WithLp.equiv_symm_apply, Pi.single_apply]
    norm_num
  · simp (config := {zeta := true}) only [g_analytical, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, PiLp.proj_apply, Pi.single_apply, mul_one, mul_zero,
      zero_add, smul_eq_mul, ite_false, ite_true, Fin.mk_one]
    unfold EuclideanSpace.single; simp only [WithLp.equiv_symm_apply, Pi.single_apply]
    norm_num

set_option linter.style.longLine false

/-- **L-Smoothness**: The gradient is Lipschitz with $L_{smooth} = 20$. -/
theorem advanced_L_smooth : is_L_smooth L_advanced 20 := by
  constructor
  · norm_num
  · intro w v
    simp_rw [gradient_advanced_eq]
    have h1 : 0 ≤ ‖exact_gradient_advanced w - exact_gradient_advanced v‖ := norm_nonneg _
    have h2 : 0 ≤ 20 * ‖w - v‖ := mul_nonneg (by norm_num) (norm_nonneg _)
    rw [← abs_of_nonneg h1, ← abs_of_nonneg h2, ← sq_le_sq]
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, 
        Fin.sum_univ_two]
    simp (config := {zeta := true}) [Pi.sub_apply, exact_gradient_advanced, 
      ite_true, ite_false, Real.norm_eq_abs, RCLike.norm_sq_eq_def, zero_pow, 
      add_zero, sq_abs]
    ring_nf
    nlinarith [sq_nonneg (v 0 - w 0), sq_nonneg (v 1 - w 1)]

/-- **Strong Convexity**: The function is $\mu$-strongly convex with $\mu = 2$. -/
theorem advanced_strongly_convex : is_strongly_convex L_advanced 2 := by
  constructor
  · norm_num
  · intro w v
    simp (config := {zeta := true}) [gradient_advanced_eq, L_advanced, 
      exact_gradient_advanced, inner, PiLp.inner_apply, EuclideanSpace.norm_sq_eq, 
      Fin.sum_univ_two, Pi.sub_apply, starRingEnd_apply, id_eq, ite_true, ite_false, 
      Real.norm_eq_abs, zero_pow, add_zero, star_trivial, RCLike.norm_sq_eq_def, sq_abs, 
      mul_one, smul_eq_mul, RCLike.inner_apply]
    ring_nf
    nlinarith [sq_nonneg (v 0 - w 0), sq_nonneg (v 1 - w 1)]

end LeanSharp.AdvancedToy
