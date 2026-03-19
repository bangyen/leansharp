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

* `hessianQuadraticForm`: Computes the curvature $v^T H v$.
* `localCurvatureMatrix`: Names the Hessian as the local curvature operator.
* `GeneralizedFilterCondition`: Abstract curvature contract for filtered directions.

## Main theorems

* `zsharp_curvature_bound`: Proves that the curvature along the filtered gradient
  is bounded by the landscape's $L_2$ sharpness and the original gradient norm.
* `generalized_filter_condition_of_spectral_bound`: Lifts spectral bounds to the
  generalized filter contract under a norm-contraction hypothesis.
-/

namespace LeanSharp

open Real ContinuousLinearMap

variable {ι : Type*} [Fintype ι]

/-- The quadratic form $v^T H v$ for some vector $v$ and Hessian $H$. -/
noncomputable def hessianQuadraticForm (L : W ι → ℝ) (w v : W ι) : ℝ :=
  @inner ℝ (W ι) _ v ((hessian L w) v)

/-- The local curvature matrix/operator at `w`.
This wrapper exists so downstream statements can depend on a stable curvature symbol
without committing to Hessian-specific implementation details in every theorem. -/
noncomputable def localCurvatureMatrix (L : W ι → ℝ) (w : W ι) : W ι →L[ℝ] W ι :=
  hessian L w

/-- Generalized filter condition for curvature-aware descent:
the filtered direction `g_filtered` must satisfy a curvature upper bound relative to
the baseline direction `g_base`. This contract exists to decouple filter design from
the specific spectral argument used to certify it. -/
def GeneralizedFilterCondition
    (H : W ι →L[ℝ] W ι) (g_base g_filtered : W ι) (κ : ℝ) : Prop :=
  @inner ℝ (W ι) _ g_filtered (H g_filtered) ≤ κ * ‖g_base‖ ^ 2

/-- Bundles a local curvature operator (Hessian) with its spectral characteristics. -/
structure CurvatureCertificate (ι : Type*) [Fintype ι] where

  /-- The loss function. -/
  L : W ι → ℝ

  /-- The point at which the curvature is evaluated. -/
  w : W ι

  /-- Proof that the Hessian is symmetric. -/
  h_symm : (hessian L w).toLinearMap.IsSymmetric

  /-- The sharpness (max eigenvalue) at this point. -/
  sharpness_val : ℝ

  /-- Proof that the sharpness is non-negative. -/
  sharpness_nonneg : 0 ≤ sharpness_val

  /-- Proof that the quadratic form is bounded by sharpness. -/
  spectral_bound : ∀ v, hessianQuadraticForm L w v ≤ sharpness_val * ‖v‖ ^ 2

/-- **ZSharp Curvature Bound**: Proves that the quadratic curvature along the
Z-score filtered gradient's direction is strictly bounded.

The bound is `sharpness * ‖g‖²`, connecting the geometric sharpness to
the statistical filter. -/
theorem zsharp_curvature_bound (C : CurvatureCertificate ι) (g : W ι) (z : ℝ) :
    hessianQuadraticForm C.L C.w (filteredGradient g z) ≤ C.sharpness_val * ‖g‖ ^ 2 := by
  apply (C.spectral_bound _).trans
  apply mul_le_mul_of_nonneg_left (norm_sq_filteredGradient_le g z) C.sharpness_nonneg

/-- Lifts a spectral curvature bound plus a norm-contraction witness into the
generalized filter condition. This theorem exists so new filters only need to provide
an abstract contraction proof to reuse the same curvature argument. -/
theorem generalized_filter_condition_of_spectral_bound
    (H : W ι →L[ℝ] W ι) (g_base g_filtered : W ι) (κ : ℝ)
    (h_spectral : ∀ v : W ι, @inner ℝ (W ι) _ v (H v) ≤ κ * ‖v‖ ^ 2)
    (hκ_nonneg : 0 ≤ κ)
    (h_contract : ‖g_filtered‖ ^ 2 ≤ ‖g_base‖ ^ 2) :
    GeneralizedFilterCondition H g_base g_filtered κ := by
  unfold GeneralizedFilterCondition
  exact (h_spectral g_filtered).trans (mul_le_mul_of_nonneg_left h_contract hκ_nonneg)

end LeanSharp
