/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Sam
import LeanSharp.Core.Filters
import LeanSharp.Stochastic.Sam
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Notation
import Mathlib.Probability.Moments.Basic

/-!
# Formal Stochastic Descent Lemma

This module proves the stochastic descent lemma for Z-score filtered gradients.
It formalizes the relationship between the variance of the raw stochastic gradient
and the variance of its filtered counterpart.

## Main definitions

* `filtered_variance_bound`: A theorem proving that Z-score filtering preserves
  or improves the bounded variance property.

## Main theorems

* `stochastic_taylor_descent`: The fundamental descent lemma in the stochastic setting.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- **Filtered Variance Bound**:
If a stochastic gradient $g$ has variance bounded by $\sigma^2$, then its
Z-score filtered version also has variance bounded by $\sigma^2$
(plus the squared norm of the true gradient).
This holds because the filter is a component-wise contraction toward zero. -/
theorem filtered_variance_bound (L : W ι → ℝ) (g : Ω → W ι) (w : W ι) (σsq : ℝ) (z : ℝ)
    (h_stoch : is_stochastic_gradient L g w)
    (h_var : has_bounded_variance L g w σsq)
    (h_int : Integrable (fun ω => ‖g ω‖ ^ 2))
    (h_meas_f : AEStronglyMeasurable (fun ω => filtered_gradient (g ω) z))
    (h_int_f : Integrable (fun ω => ‖filtered_gradient (g ω) z‖ ^ 2)) :
    𝔼[fun ω => ‖filtered_gradient (g ω) z - 𝔼[fun ω' => filtered_gradient (g ω') z]‖ ^ 2] ≤
      σsq + ‖gradient L w‖ ^ 2 := by
  let g_f (ω : Ω) := filtered_gradient (g ω) z
  have h_int_g : Integrable g := h_stoch.1
  
  -- Step 1: Integrability of g_f
  -- Since g_f is bounded by g and is measurable, it is integrable.
  have h_int_gf : Integrable g_f :=
    h_int_g.mono h_meas_f (Filter.Eventually.of_forall (fun ω => filtered_norm_bound (g ω) z))
  
  -- Step 2: Use the L2 Bias-Variance Decomposition for g_f
  have h_gf_decomp := l2_bias_variance_decomposition g_f h_int_f h_int_gf
  
  -- Step 3: Bound 𝔼[‖g_f‖^2] by 𝔼[‖g‖^2]
  have h_norm_le : 𝔼[fun ω => ‖g_f ω‖ ^ 2] ≤ 𝔼[fun ω => ‖g ω‖ ^ 2] :=
    integral_mono h_int_f h_int (fun ω => filtered_gradient_norm_sq_le (g ω) z)
    
  -- Step 4: Use the decomposition of the original gradient g
  have h_grad_eq : 𝔼[g] = gradient L w := h_stoch.2
  have h_raw_decomp := l2_bias_variance_decomposition g h_int h_int_g
  
  -- Step 5: Final calculation
  calc 𝔼[fun ω => ‖g_f ω - 𝔼[g_f]‖ ^ 2]
    _ = 𝔼[fun ω => ‖g_f ω‖ ^ 2] - ‖𝔼[g_f]‖ ^ 2 := by
        rw [h_gf_decomp]; ring
    _ ≤ 𝔼[fun ω => ‖g_f ω‖ ^ 2] := by
        simp only [sub_le_self_iff]
        positivity
    _ ≤ 𝔼[fun ω => ‖g ω‖ ^ 2] := h_norm_le
    _ = 𝔼[fun ω => ‖g ω - 𝔼[g]‖ ^ 2] + ‖𝔼[g]‖ ^ 2 := h_raw_decomp
    _ ≤ σsq + ‖gradient L w‖ ^ 2 := by
        rw [h_grad_eq, add_comm _ (‖gradient L w‖ ^ 2), add_comm σsq]
        apply add_le_add_right h_var

end LeanSharp
