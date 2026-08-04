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
# Ill-Conditioned Landscape - Basic Definitions

This module provides the core definitions and derivative proofs for a quadratic
landscape with high condition number.

## Main Definitions
* `advancedLoss`: An ill-conditioned 2D quadratic loss function.
* `exactGradientAdvanced`: Analytical gradient of `advancedLoss`.

## Main Theorems
* `hasFDerivAt_advancedLoss`: Proves the analytical derivative of `advancedLoss`.
* `gradient_advanced_eq`: Shows that the computed gradient matches the analytical one.
-/

namespace LeanSharp.IllConditioned

open BigOperators

local notation "W2" => W (Fin 2)

/-- An ill-conditioned 2D quadratic loss function $L(w_0, w_1) = 10w_0^2 + w_1^2$. -/
noncomputable def advancedLoss (w : W2) : ℝ :=
  10 * (w 0) ^ 2 + (w 1) ^ 2

/-- The analytical gradient is $\nabla L(w) = [20w_0, 2w_1]$. -/
noncomputable def exactGradientAdvanced (w : W2) : W2 :=
  WithLp.equiv 2 (Fin 2 → ℝ) |>.symm fun i =>
    if i = 0 then 20 * w 0
    else 2 * w 1

/-- The analytical Fréchet derivative of $L_{advanced}$. -/
lemma hasFDerivAt_advancedLoss (w : W2) :
    HasFDerivAt advancedLoss (((20 : ℝ) * w 0) • (EuclideanSpace.proj 0 : W2 →L[ℝ] ℝ) +
      ((2 : ℝ) * w 1) • (EuclideanSpace.proj 1 : W2 →L[ℝ] ℝ)) w := by
  rw [show advancedLoss = fun w : W2 => 10 * (w 0) ^ 2 + (w 1) ^ 2 by ext; rfl]
  convert hasFDerivAt_quadratic 10 1 w using 1
  · ext x; simp only [one_mul]
  · ring_nf

theorem gradient_advanced_eq (w : W2) :
    gradient advancedLoss w = exactGradientAdvanced w := by
  let g_analytical : W2 →L[ℝ] ℝ := ((20 : ℝ) * w 0) • EuclideanSpace.proj 0 +
    ((2 : ℝ) * w 1) • EuclideanSpace.proj 1
  have hL : HasFDerivAt advancedLoss g_analytical w := hasFDerivAt_advancedLoss w
  unfold gradient
  rw [hL.fderiv]
  ext i
  unfold exactGradientAdvanced
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

end LeanSharp.IllConditioned
