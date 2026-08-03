/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Core.Taylor.SmoothDescent

/-!
# Taylor SAM Bounds

This module exists to isolate SAM-specific consequences of smoothness descent so
SAM recurrence proofs can depend on a focused interface.

## Theorems

* `sam_taylor_bound`: smoothness-based upper bound on the SAM objective.
* `z_sharp_gap_benefit`: gradient-norm contraction benefit of the filter.
-/

namespace LeanSharp

open Set InnerProductSpace Real NNReal

variable {ι : Type*} [Fintype ι]

/-- **SAM Taylor Terms Bound**: Auxiliary lemma to bound the SAM objective terms. -/
private lemma sam_taylor_terms_bound (M : ℝ≥0) (ρ : ℝ) (hρ : 0 ≤ ρ) (g ε : W ι)
    (h_norm : ‖ε‖ ≤ ρ) :
    inner ℝ g ε + (M : ℝ) / 2 * ‖ε‖ ^ 2 ≤ ‖g‖ * ρ + (M : ℝ) / 2 * ρ ^ 2 := by
  have hcs : inner ℝ g ε ≤ ‖g‖ * ρ := by
    calc inner ℝ g ε ≤ ‖g‖ * ‖ε‖ := real_inner_le_norm _ _
      _ ≤ ‖g‖ * ρ := mul_le_mul_of_nonneg_left h_norm (norm_nonneg _)
  have hsq : (M : ℝ) / 2 * ‖ε‖ ^ 2 ≤ (M : ℝ) / 2 * ρ ^ 2 := by
    apply mul_le_mul_of_nonneg_left (sq_le_sq.mpr (by
      simp only [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hρ, h_norm]))
    apply div_nonneg (NNReal.coe_nonneg M)
    norm_num
  linarith

/-- **Gradient Norm Contraction (SAM Complexity Benefit)**:
    The term controlling the generalization gap is reduced by the filter. -/
theorem z_sharp_gap_benefit (g : W ι) (z : ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ‖filteredGradient g z‖ * ρ ≤ ‖g‖ * ρ := by
  have h_contract := norm_filtered_gradient_le g z
  nlinarith

/-- **SAM Taylor Bound**: `samObjective L w ρ ≤ L w + ‖∇L(w)‖ * ρ + M/2 * ρ²`. -/
theorem sam_taylor_bound (L : SmoothObjective ι) (w : W ι) (ρ : ℝ)
    (hρ : 0 ≤ ρ) :
    samObjective L.toFun w ρ ≤
      L.toFun w + ‖gradient L.toFun w‖ * ρ + (L.smoothness : ℝ) / 2 * ρ ^ 2 := by
  unfold samObjective perturbationNeighborhood
  apply csSup_le
  · exact ⟨L.toFun w, w, ⟨
      0,
      by simpa only [Metric.mem_closedBall, dist_self] using hρ,
      by simp only [add_zero]
    ⟩, rfl⟩
  · rintro v ⟨_, ⟨ε, hε_norm, rfl⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hε_norm
    have hdescent := smooth_descent L w ε
    have h_terms := sam_taylor_terms_bound L.smoothness ρ hρ (gradient L.toFun w) ε hε_norm
    linarith [hdescent, h_terms]

end LeanSharp
