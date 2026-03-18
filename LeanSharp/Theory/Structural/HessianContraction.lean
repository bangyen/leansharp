/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Core.Landscape
import LeanSharp.Theory.Dynamics.Generalization
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Hessian Contraction

This module formalizes the relationship between the geometric properties of the
loss landscape and the statistical Z-score gradient filter.

## Main definitions

* `hessian_quadratic_form`: Computes the curvature $v^T H v$.
* `local_curvature_matrix`: Names the Hessian as the local curvature operator.
* `generalized_filter_condition`: Abstract curvature contract for filtered directions.

## Main theorems

* `zsharp_curvature_bound`: Proves that the curvature along the filtered gradient
  is bounded by the landscape's $L_2$ sharpness and the original gradient norm.
* `generalized_filter_condition_of_spectral_bound`: Lifts spectral bounds to the
  generalized filter contract under a norm-contraction hypothesis.
* `zsharp_generalized_filter_condition`: Instantiates the generalized filter contract
  for Z-score filtered gradients.
-/

namespace LeanSharp

open Real ContinuousLinearMap

variable {ι : Type*} [Fintype ι]

/-- The quadratic form $v^T H v$ for some vector $v$ and Hessian $H$. -/
noncomputable def hessian_quadratic_form (L : W ι → ℝ) (w v : W ι) : ℝ :=
  @inner ℝ (W ι) _ v ((hessian L w) v)

/-- The local curvature matrix/operator at `w`.
This wrapper exists so downstream statements can depend on a stable curvature symbol
without committing to Hessian-specific implementation details in every theorem. -/
noncomputable def local_curvature_matrix (L : W ι → ℝ) (w : W ι) : W ι →L[ℝ] W ι :=
  hessian L w

/-- Generalized filter condition for curvature-aware descent:
the filtered direction `g_filtered` must satisfy a curvature upper bound relative to
the baseline direction `g_base`. This contract exists to decouple filter design from
the specific spectral argument used to certify it. -/
def generalized_filter_condition
    (H : W ι →L[ℝ] W ι) (g_base g_filtered : W ι) (κ : ℝ) : Prop :=
  @inner ℝ (W ι) _ g_filtered (H g_filtered) ≤ κ * ‖g_base‖ ^ 2

/-- **ZSharp Curvature Bound**: Proves that the quadratic curvature along the
Z-score filtered gradient's direction is strictly bounded.

The bound is $\lambda_{max} \|g\|^2$, connecting the geometric sharpness to
the statistical filter. -/
theorem zsharp_curvature_bound (L : W ι → ℝ) (w : W ι) (g : W ι) (z : ℝ)
    (hT : (hessian L w).toLinearMap.IsSymmetric)
    (h_spectral : ∀ v : W ι, hessian_quadratic_form L w v ≤ sharpness L w hT * ‖v‖ ^ 2)
    (h_sharpness_nonneg : 0 ≤ sharpness L w hT) :
    hessian_quadratic_form L w (filtered_gradient g z) ≤ sharpness L w hT * ‖g‖ ^ 2 := by
  apply (h_spectral _).trans
  apply mul_le_mul_of_nonneg_left (filtered_gradient_norm_sq_le g z) h_sharpness_nonneg

/-- Lifts a spectral curvature bound plus a norm-contraction witness into the
generalized filter condition. This theorem exists so new filters only need to provide
an abstract contraction proof to reuse the same curvature argument. -/
theorem generalized_filter_condition_of_spectral_bound
    (H : W ι →L[ℝ] W ι) (g_base g_filtered : W ι) (κ : ℝ)
    (h_spectral : ∀ v : W ι, @inner ℝ (W ι) _ v (H v) ≤ κ * ‖v‖ ^ 2)
    (hκ_nonneg : 0 ≤ κ)
    (h_contract : ‖g_filtered‖ ^ 2 ≤ ‖g_base‖ ^ 2) :
    generalized_filter_condition H g_base g_filtered κ := by
  unfold generalized_filter_condition
  exact (h_spectral g_filtered).trans (mul_le_mul_of_nonneg_left h_contract hκ_nonneg)

/-- Instantiates the generalized filter condition for Z-score filtering by combining
the sharpness spectral bound with the known filtered-gradient norm contraction. -/
theorem zsharp_generalized_filter_condition
    (L : W ι → ℝ) (w : W ι) (g : W ι) (z : ℝ)
    (hT : (hessian L w).toLinearMap.IsSymmetric)
    (h_spectral : ∀ v : W ι, hessian_quadratic_form L w v ≤ sharpness L w hT * ‖v‖ ^ 2)
    (h_sharpness_nonneg : 0 ≤ sharpness L w hT) :
    generalized_filter_condition (local_curvature_matrix L w) g (filtered_gradient g z)
      (sharpness L w hT) := by
  unfold generalized_filter_condition local_curvature_matrix
  exact zsharp_curvature_bound L w g z hT h_spectral h_sharpness_nonneg

end LeanSharp
