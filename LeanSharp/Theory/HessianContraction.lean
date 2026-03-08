/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Landscape
import LeanSharp.Core.Filters
import LeanSharp.Theory.Generalization
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Hessian Contraction

This module formalizes the relationship between the geometric properties of the
loss landscape and the statistical Z-score gradient filter.

## Main definitions

* `hessian_quadratic_form`: Computes the curvature $v^T H v$.

## Main theorems

* `zsharp_curvature_bound`: Proves that the curvature along the filtered gradient
  is bounded by the landscape's $L_2$ sharpness and the original gradient norm.
-/

namespace LeanSharp

open Real ContinuousLinearMap

variable {d : ℕ}

/-- The quadratic form $v^T H v$ for some vector $v$ and Hessian $H$. -/
noncomputable def hessian_quadratic_form (L : W d → ℝ) (w v : W d) : ℝ :=
  @inner ℝ (W d) _ v ((hessian L w) v)


/-- **Curvature Scaling Lemma**: Proves that the curvature of a vector scaled by
the squared norm's contraction factor is correctly bounded. -/
private lemma curvature_norm_scale_le (L : W d → ℝ) (w v g : W d)
    (hT : (hessian L w).toLinearMap.IsSymmetric)
    (h_spectral : ∀ u : W d, hessian_quadratic_form L w u ≤ sharpness L w hT * ‖u‖ ^ 2)
    (h_sharpness_nonneg : 0 ≤ sharpness L w hT)
    (h_norm_le : ‖v‖ ^ 2 ≤ ‖g‖ ^ 2) :
    hessian_quadratic_form L w v ≤ sharpness L w hT * ‖g‖ ^ 2 :=
  (h_spectral v).trans (mul_le_mul_of_nonneg_left h_norm_le h_sharpness_nonneg)

/-- **ZSharp Curvature Bound**: Proves that the quadratic curvature along the
Z-score filtered gradient's direction is strictly bounded.

The bound is $\lambda_{max} \|g\|^2$, connecting the geometric sharpness to
the statistical filter. -/
theorem zsharp_curvature_bound (L : W d → ℝ) (w : W d) (g : W d) (z : ℝ)
    (hT : (hessian L w).toLinearMap.IsSymmetric)
    (h_spectral : ∀ v : W d, hessian_quadratic_form L w v ≤ sharpness L w hT * ‖v‖ ^ 2)
    (h_sharpness_nonneg : 0 ≤ sharpness L w hT) :
    hessian_quadratic_form L w (filtered_gradient g z) ≤ sharpness L w hT * ‖g‖ ^ 2 :=
  curvature_norm_scale_le L w (filtered_gradient g z) g hT h_spectral h_sharpness_nonneg
    (filtered_gradient_norm_sq_le g z)

end LeanSharp
