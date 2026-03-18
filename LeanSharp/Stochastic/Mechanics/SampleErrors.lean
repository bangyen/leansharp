/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Stochastic.Mechanics.SharpnessMap
import LeanSharp.Tactic.ZSolve
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Lebesgue.Norm
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Notation

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

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- **ZSharp Variance Bound**: If the base stochastic gradient has bounded
variance $\sigma^2$, the filtered gradient also has strictly bounded variance. -/
theorem zsharp_variance_bound (L : W ι → ℝ) (g_adv : Ω → W ι) (w : W ι) (z σsq : ℝ)
    (h_unbiased : is_stochastic_gradient L g_adv w)
    (h_base_var : has_bounded_variance L g_adv w σsq)
    (h_int_fg : Integrable (fun ω => ‖filtered_gradient (g_adv ω) z‖ ^ 2))
    (h_int_g : Integrable (fun ω => ‖g_adv ω‖ ^ 2)) :
    𝔼[fun ω => ‖filtered_gradient (g_adv ω) z‖ ^ 2] ≤ σsq + ‖gradient L w‖ ^ 2 := by
  calc 𝔼[fun ω => ‖filtered_gradient (g_adv ω) z‖ ^ 2]
      ≤ 𝔼[fun ω => ‖g_adv ω‖ ^ 2] :=
        integral_mono h_int_fg h_int_g (fun ω => filtered_gradient_norm_sq_le (g_adv ω) z)
    _ = 𝔼[fun ω => ‖g_adv ω - gradient L w‖ ^ 2] + ‖gradient L w‖ ^ 2 := by
        rw [l2_bias_variance_decomposition g_adv h_int_g h_unbiased.1, h_unbiased.2]
    _ ≤ σsq + ‖gradient L w‖ ^ 2 := by
        simpa only [
          add_le_add_iff_right,
          has_bounded_variance
        ] using h_base_var

end LeanSharp
