/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.StochasticSam
import LeanSharp.Core.Filters
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Probability.Notation
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Norm
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import LeanSharp.Tactic.ZSolve

/-!
# Stochastic Generalization Bounds

This module formalizes advanced bounds on the variance of the ZSharp algorithm
in stochastic settings.

A key theoretical property of the Z-score filter is that it is a contraction
with respect to the $L_2$ norm. This ensures that the filtered gradient does
not increase the variance of the stochastic estimator.

## Main theorems

* `filtered_norm_bound`: Proves the $L_2$ norm contraction of the filter.
* `zsharp_variance_bound`: Proves that the variance of the filtered stochastic
  gradient is bounded by the variance of the original estimator plus a
  curvature term.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {d : ℕ}
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

omit [IsProbabilityMeasure (volume : Measure Ω)] in
/-- **Filtered Variance Contraction**: The L2 norm contraction of the filter ensures
that the filtered gradient expectation is bounded by the original. -/
lemma filtered_variance_contraction (g : Ω → W d) (z : ℝ)
    (h_int_fg : Integrable (fun ω => ‖filtered_gradient (g ω) z‖ ^ 2))
    (h_int_g : Integrable (fun ω => ‖g ω‖ ^ 2)) :
    𝔼[fun ω => ‖filtered_gradient (g ω) z‖ ^ 2] ≤ 𝔼[fun ω => ‖g ω‖ ^ 2] :=
  integral_mono h_int_fg h_int_g (by intro ω; exact filtered_gradient_norm_sq_le (g ω) z)

/-- **ZSharp Variance Bound**: If the base stochastic gradient has bounded
variance $\sigma^2$, the filtered gradient also has strictly bounded variance. -/
theorem zsharp_variance_bound (L : W d → ℝ) (g_adv : Ω → W d) (w : W d) (z σsq : ℝ)
    (h_unbiased : is_stochastic_gradient L g_adv w)
    (h_base_var : has_bounded_variance L g_adv w σsq)
    (h_int_fg : Integrable (fun ω => ‖filtered_gradient (g_adv ω) z‖ ^ 2))
    (h_int_g : Integrable (fun ω => ‖g_adv ω‖ ^ 2)) :
    𝔼[fun ω => ‖filtered_gradient (g_adv ω) z‖ ^ 2] ≤ σsq + ‖gradient L w‖ ^ 2 := by
  -- Step 1: Use the Filtered Variance Contraction lemma
  have h_exp_bound := filtered_variance_contraction g_adv z h_int_fg h_int_g
  -- Step 2: Expand the base expectation using the Bias-Variance Decomposition helper lemma
  have h_var_expansion : 𝔼[fun ω => ‖g_adv ω‖ ^ 2] =
                          𝔼[fun ω => ‖g_adv ω - gradient L w‖ ^ 2] + ‖gradient L w‖ ^ 2 := by
    rw [l2_bias_variance_decomposition g_adv h_int_g h_unbiased.1]
    rw [h_unbiased.2]
  -- Step 3: Combine the contraction and decomposition to reach the final variance bound
  calc 𝔼[fun ω => ‖filtered_gradient (g_adv ω) z‖ ^ 2]
      ≤ 𝔼[fun ω => ‖g_adv ω‖ ^ 2] := h_exp_bound
    _ = 𝔼[fun ω => ‖g_adv ω - gradient L w‖ ^ 2] + ‖gradient L w‖ ^ 2 := h_var_expansion
    _ ≤ σsq + ‖gradient L w‖ ^ 2 := by
      have h_var := h_base_var
      unfold has_bounded_variance at h_var
      linarith

end LeanSharp
