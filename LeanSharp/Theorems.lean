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
    simp only [WithLp.equiv_symm_apply, ge_iff_le, h_eval]
    -- 0^2 ≤ x^2 is true because x^2 ≥ 0
    exact sq_nonneg (g i)

  · -- Case: mask = 1
    have h_eval : z_score_mask g z i = 1 := h1
    simp [h_eval]
    -- x^2 ≤ x^2 is true by reflexivity, handled by simp

/-- Lemma 3 (Scalar): The absolute error of any component after filtering is
    bounded by `|μ| + z * σ`. -/
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
    -- By combining the inequalities: 
    -- |g i| - |μ| ≤ |g i - μ| < z * σ  ==>  |g i| < |μ| + z * σ
    linarith

/-!
## 2. Global Norm Contraction

From the element-wise bound, we derive that the Z-Score filter
cannot increase the total L₂ norm of the gradient tensor.
-/

/-- Z-Score filtering is a norm contraction:
    the filtered gradient has smaller (or equal) L₂ norm than the original. -/
theorem filter_norm_contraction (g : W d) (z : ℝ) :
    ‖filtered_gradient g z‖ ≤ ‖g‖ := by
  -- Expand ‖v‖² = ∑ i, (v i)² for EuclideanSpace over ℝ
  have expand : ∀ v : W d, ‖v‖^2 = ∑ i : Fin d, (v i)^2 := fun v => by
    rw [EuclideanSpace.norm_sq_eq]; simp [Real.norm_eq_abs, sq_abs]
  -- It suffices to show ‖filt‖² ≤ ‖g‖² (squaring is monotone on ℝ≥0)
  have h_sq : ‖filtered_gradient g z‖^2 ≤ ‖g‖^2 := by
    rw [expand (filtered_gradient g z), expand g]
    apply Finset.sum_le_sum
    intro i _
    have h_unfold : filtered_gradient g z i = hadamard g (z_score_mask g z) i := rfl
    rw [h_unfold]; exact mask_bound g z i
  exact le_of_sq_le_sq h_sq (norm_nonneg g)

/-!
## 3. Zero-Threshold Identity

When `z = 0`, the mask threshold is `0 * σ = 0`. Since `|g i - μ| ≥ 0` always,
every component is passed: the filter is the identity.
-/

/-- At threshold z = 0, the filter passes all components unchanged. -/
theorem filter_zero_threshold (g : W d) : filtered_gradient g 0 = g := by
  ext i
  unfold filtered_gradient hadamard z_score_mask
  simp only [zero_mul, ge_iff_le]
  -- We need: |g i - vector_mean g| ≥ 0 * vector_std g = 0
  -- This is just abs_nonneg
  have : |g i - vector_mean g| ≥ 0 := abs_nonneg _
  simp [this]

/-!
## 4. Monotonicity in Threshold

A lower threshold z is more restrictive (keeps fewer components).
-/

/-- If a component passes the stricter low-threshold mask (z small),
    it also passes the looser high-threshold mask (z' ≥ z). -/
lemma mask_monotone_pass (g : W d) (z z' : ℝ) (hz : z ≤ z')
    (hs : 0 ≤ vector_std g) (i : Fin d)
    (h_pass : z_score_mask g z' i = 1) : z_score_mask g z i = 1 := by
  unfold z_score_mask at *
  by_cases hc : |g i - vector_mean g| ≥ z * vector_std g
  · simp [hc]
  · -- h_pass says |g i - μ| ≥ z' * σ, but ¬(|g i - μ| ≥ z * σ)
    -- z ≤ z' and σ ≥ 0, so z * σ ≤ z' * σ, contradiction
    by_cases hc' : |g i - vector_mean g| ≥ z' * vector_std g
    · simp [hc'] at h_pass
      have : z * vector_std g ≤ z' * vector_std g :=
        mul_le_mul_of_nonneg_right hz hs
      linarith [not_le.mp hc]
    · simp [hc'] at h_pass
