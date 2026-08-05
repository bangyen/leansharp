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
* `advancedLossBundled`: The bundled strongly convex objective.
* `advancedTwiceDifferentiable`: A `TwiceDifferentiable` witness.

## Main Theorems
* `advanced_L_smooth`: The gradient is Lipschitz with $L = 20$.
* `advanced_strongly_convex`: The function is $\mu$-strongly convex.
* `advanced_IsSmooth`: The ill-conditioned bowl satisfies the Taylor descent bound.
-/

namespace LeanSharp.IllConditioned

open BigOperators

local notation "W2" => W (Fin 2)

/-- **L-Smoothness**: The gradient is Lipschitz with $L_{smooth} = 20$. -/
theorem advanced_L_smooth : IsLSmooth advancedLoss 20 := by
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
theorem advanced_strongly_convex : IsStronglyConvex advancedLoss 2 := by
  constructor
  · norm_num
  · intro w v
    simp only [
      advancedLoss,
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
noncomputable def advancedLossBundled : StronglyConvexObjective (Fin 2) where
  toFun := advancedLoss
  smoothness := 20
  differentiable := fun _ => (hasFDerivAt_advancedLoss _).differentiableAt
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro w v; simpa only [dist_eq_norm] using advanced_L_smooth.2 w v
  μ := 2
  strongly_convex := advanced_strongly_convex

/-- **Taylor Smoothness**: the ill-conditioned bowl satisfies the Taylor descent bound
`advancedLoss y ≤ advancedLoss x + ⟨∇advancedLoss x, y - x⟩ + 10‖y - x‖²`, i.e.
`IsSmooth advancedLoss 20`. This discharges the descent lemma's smoothness hypothesis. -/
theorem advanced_IsSmooth : IsSmooth advancedLoss 20 := by
  intro x y
  rw [gradient_advanced_eq]
  simp only [exactGradientAdvanced, advancedLoss, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, Fin.sum_univ_two, WithLp.equiv_symm_apply, PiLp.sub_apply, ↓reduceIte,
    EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  ring_nf
  norm_num
  nlinarith [sq_nonneg (y 1 - x 1)]

/-- **Twice Differentiable**: the ill-conditioned bowl is `ContDiff ℝ 2`, so it is a
`TwiceDifferentiable` witness for the Hessian machinery. -/
noncomputable def advancedTwiceDifferentiable : TwiceDifferentiable (Fin 2) where
  toFun := advancedLoss
  differentiable := by
    rw [show advancedLoss = fun x : W (Fin 2) => 10 * (x 0) ^ 2 + (x 1) ^ 2
        by ext x; simp only [advancedLoss]]
    apply ContDiff.add
    · have h0 : ContDiff ℝ 2 (fun x : W (Fin 2) => (x 0) ^ 2) := by
        simpa only [sq] using (contDiff_piLp_apply (p := 2) (i := (0 : Fin 2))).mul
          (contDiff_piLp_apply (p := 2) (i := (0 : Fin 2)))
      exact ContDiff.mul (contDiff_const : ContDiff ℝ 2 (fun _ : W (Fin 2) => (10 : ℝ))) h0
    · simpa only [sq] using (contDiff_piLp_apply (p := 2) (i := (1 : Fin 2))).mul
        (contDiff_piLp_apply (p := 2) (i := (1 : Fin 2)))

end LeanSharp.IllConditioned
