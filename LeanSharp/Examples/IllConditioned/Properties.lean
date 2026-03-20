/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Examples.IllConditioned.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith

/-!
# Ill-Conditioned Landscape - Properties

This module establishes smoothness and convexity properties for the
ill-conditioned quadratic objective.

## Main Definitions
* `SmoothObjective`: Uses the bundled assumption structure.

## Main Theorems
* `smooth_advanced`: Proof of $L$-smoothness.
* `convex_advanced`: Proof of strong convexity.
-/

namespace LeanSharp.IllConditioned

open BigOperators

local notation "W2" => W (Fin 2)

/-- **L-Smoothness**: The gradient is Lipschitz with $L_{smooth} = 20$. -/
theorem advanced_L_smooth : IsLSmooth L_advanced 20 := by
  constructor
  · norm_num
  · intro w v
    rw [gradient_advanced_eq, gradient_advanced_eq]
    have h1 : 0 ≤ ‖exactGradientAdvanced w - exactGradientAdvanced v‖ := norm_nonneg _
    have h2 : 0 ≤ 20 * ‖w - v‖ := mul_nonneg (by norm_num) (norm_nonneg _)
    rw [← abs_of_nonneg h1, ← abs_of_nonneg h2, ← sq_le_sq]
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two,
        Fin.sum_univ_two]
    simp only [
      Fin.isValue,
      exactGradientAdvanced,
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
theorem advanced_strongly_convex : IsStronglyConvex L_advanced 2 := by
  constructor
  · norm_num
  · intro w v
    simp only [
      L_advanced,
      Fin.isValue,
      inner,
      gradient_advanced_eq,
      exactGradientAdvanced,
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
