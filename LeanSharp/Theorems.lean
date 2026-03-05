import LeanSharp.Filters
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.ByCases

set_option linter.unusedSectionVars false

/-!
# Phase 1: Property Proofs of the Filter

This file contains the formal proofs for the properties of the Z-Score
Gradient Filtering operation.

## 1. Norm Contraction

The fundamental property of the Z-Score filter (and any binary mask)
is that it reduces or preserves the $L_2$ norm of the gradient tensor,
acting as a contraction.
-/

namespace LeanSharp

variable {d : ℕ} [Fact (0 < d)]

/-- The elements of the z-score mask are strictly binary (either `0` or `1`). -/
theorem z_score_mask_binary (g : W d) (z : ℝ) (i : Fin d) :
    z_score_mask g z i = 0 ∨ z_score_mask g z i = 1 := by
  unfold z_score_mask
  by_cases h : |g i - vector_mean g| ≥ z * vector_std g
  · right; simp [h]
  · left; simp [h]

/-- The core contraction property: element-wise masking with {0, 1} reduces the absolute value. -/
lemma mask_bound (g : W d) (z : ℝ) (i : Fin d) :
    (hadamard g (z_score_mask g z) i)^2 ≤ (g i)^2 := by
  unfold hadamard
  have h_bin := z_score_mask_binary g z i
  rcases h_bin with h0 | h1
  · have h_eval : z_score_mask g z i = 0 := h0
    simp only [WithLp.equiv_symm_apply, h_eval, mul_zero]
    rw [zero_pow (by norm_num)]
    exact sq_nonneg (g i)
  · have h_eval : z_score_mask g z i = 1 := h1
    simp only [WithLp.equiv_symm_apply, h_eval, mul_one]
    exact le_refl _

/-- Lemma: The absolute error of any component after filtering is
    bounded by `|μ| + z * σ`. -/
lemma filtered_component_bound (g : W d) (z : ℝ) (hz : z ≥ 0) (i : Fin d) :
    |filtered_gradient g z i - g i| ≤ |vector_mean g| + z * vector_std g := by
  unfold filtered_gradient hadamard z_score_mask
  simp only [WithLp.equiv_symm_apply]
  by_cases h : |g i - vector_mean g| ≥ z * vector_std g
  · simp only [h, if_true, mul_one, sub_self, abs_zero]
    have h1 : 0 ≤ |vector_mean g| := abs_nonneg (vector_mean g)
    have h2 : 0 ≤ vector_std g := by
      unfold vector_std
      exact Real.sqrt_nonneg (vector_variance g)
    have h3 : 0 ≤ z * vector_std g := mul_nonneg hz h2
    linarith
  · simp only [h, if_false, mul_zero, zero_sub, abs_neg]
    have h_lt : |g i - vector_mean g| < z * vector_std g := not_le.mp h
    have h_tri := abs_add_le (g i - vector_mean g) (vector_mean g)
    have : (g i - vector_mean g) + vector_mean g = g i := by abel
    rw [this] at h_tri
    linarith

/-- Z-Score filtering is a global norm contraction:
    the filtered gradient has smaller (or equal) L₂ norm than the original. -/
theorem filter_norm_contraction (g : W d) (z : ℝ) :
    ‖filtered_gradient g z‖ ≤ ‖g‖ := by
  have expand : ∀ v : W d, ‖v‖^2 = ∑ i : Fin d, (v i)^2 := fun v => by
    rw [EuclideanSpace.norm_sq_eq]; simp [Real.norm_eq_abs, sq_abs]
  have h_sq : ‖filtered_gradient g z‖^2 ≤ ‖g‖^2 := by
    rw [expand (filtered_gradient g z), expand g]
    apply Finset.sum_le_sum
    intro i _
    have h_unfold : filtered_gradient g z i = hadamard g (z_score_mask g z) i := rfl
    rw [h_unfold]; exact mask_bound g z i
  exact le_of_sq_le_sq h_sq (norm_nonneg g)

/-- At threshold z = 0, the filter passes all components unchanged. -/
theorem filter_zero_threshold (g : W d) : filtered_gradient g 0 = g := by
  ext i
  unfold filtered_gradient hadamard z_score_mask
  simp only [zero_mul, ge_iff_le, WithLp.equiv_symm_apply]
  have : |g i - vector_mean g| ≥ 0 := abs_nonneg _
  simp [this]

/-- If a component passes the stricter low-threshold mask (z small),
    it also passes the looser high-threshold mask (z' ≥ z). -/
lemma mask_monotone_pass (g : W d) (z z' : ℝ) (hz : z ≤ z')
    (hs : 0 ≤ vector_std g) (i : Fin d)
    (h_pass : z_score_mask g z' i = 1) : z_score_mask g z i = 1 := by
  unfold z_score_mask at *
  simp only [WithLp.equiv_symm_apply] at *
  split_ifs at h_pass with h_cond
  · have : |g i - vector_mean g| ≥ z * vector_std g := by
      calc |g i - vector_mean g| ≥ z' * vector_std g := h_cond
           _                    ≥ z * vector_std g  := mul_le_mul_of_nonneg_right hz hs
    simp [this]
  · simp at h_pass

end LeanSharp
