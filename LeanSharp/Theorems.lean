import LeanSharp.Filters
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.ByCases

/-!
# Phase 1: Property Proofs of the Filter

This file contains the formal proofs for the properties of the Z-Score
Gradient Filtering operation.

## 1. Norm Contraction

The fundamental property of the Z-Score filter (and any binary mask)
is that it reduces or preserves the $L_2$ norm of the gradient tensor,
acting as a contraction.
-/

variable {d : ℕ}

/-- The elements of the z-score mask are strictly binary (either `0` or `1`). -/
theorem z_score_mask_binary (g : W d) (z : ℝ) (i : Fin d) :
    z_score_mask g z i = 0 ∨ z_score_mask g z i = 1 := by
  unfold z_score_mask
  -- Use by_cases directly on the if-condition to bypass the space mapping
  by_cases h : |g i - vector_mean g| ≥ z * vector_std g
  · right
    -- When h is true, the if-statement evaluates to 1
    simp [h]
  · left
    -- When h is false, the if-statement evaluates to 0
    simp [h]

/-- The core contraction property: element-wise masking with {0, 1} reduces the absolute value.
    Since `(1 * x)^2 = x^2` and `(0 * x)^2 = 0`, the Hadamard product's components
    are strictly bounded by the original components. -/
lemma mask_bound (g : W d) (z : ℝ) (i : Fin d) :
    (hadamard g (z_score_mask g z) i)^2 ≤ (g i)^2 := by
  unfold hadamard
  
  -- The mask is either 0 or 1
  have h_bin := z_score_mask_binary g z i
  
  rcases h_bin with h0 | h1
  · -- Case: mask = 0
    -- Rewrite the mask evaluation to 0
    have h_eval : z_score_mask g z i = 0 := h0
    simp [h_eval]
    -- 0^2 ≤ x^2 is true because x^2 ≥ 0
    exact sq_nonneg (g i)
    
  · -- Case: mask = 1
    have h_eval : z_score_mask g z i = 1 := h1
    simp [h_eval]
    -- x^2 ≤ x^2 is true by reflexivity, handled by simp

/-- Lemma 3 (Scalar): The absolute error of any component after filtering is bounded by `|μ| + z * σ`. -/
lemma filtered_component_bound (g : W d) (z : ℝ) (hz : z ≥ 0) (i : Fin d) :
    |filtered_gradient g z i - g i| ≤ |vector_mean g| + z * vector_std g := by
  unfold filtered_gradient hadamard z_score_mask
  by_cases h : |g i - vector_mean g| ≥ z * vector_std g
  · -- Case: Condition is met, mask is 1
    simp [h]
    -- We must prove 0 ≤ |μ| + z * σ.
    have h1 : 0 ≤ |vector_mean g| := abs_nonneg (vector_mean g)
    -- Variance is a sum of squares, so its square root (std) is non-negative.
    have h2 : 0 ≤ vector_std g := by
      unfold vector_std
      exact Real.sqrt_nonneg (vector_variance g)
    have h3 : 0 ≤ z * vector_std g := mul_nonneg hz h2
    linarith
  · -- Case: Condition is not met, mask is 0. 
    -- It simplifies to evaluating |-g i| ≤ |μ| + z * σ, which is |g i| ≤ |μ| + z * σ
    simp [h]
    -- We know ¬(|g i - μ| ≥ z * σ), so |g i - μ| < z * σ
    have h_lt : |g i - vector_mean g| < z * vector_std g := not_le.mp h
    -- By the reverse triangle inequality: |a| - |b| ≤ |a - b|
    have h_triangle : |g i| - |vector_mean g| ≤ |g i - vector_mean g| := 
      abs_sub_abs_le_abs_sub (g i) (vector_mean g)
    -- By combining the inequalities: |g i| - |μ| ≤ |g i - μ| < z * σ  ==>  |g i| < |μ| + z * σ
    linarith
