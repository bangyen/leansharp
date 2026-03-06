/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Sam
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Z-Score Gradient Filtering

This module formalizes the statistical filtering of gradient tensors using
Z-score masking.

## Main definitions

* `vector_mean`: The empirical mean of a vector's components.
* `vector_variance`: The empirical variance of a vector's components.
* `vector_std`: The standard deviation of a vector's components.
* `z_score_mask`: A boolean-valued vector in $\{0, 1\}^d$ indicating components
  within the Z-score threshold.
* `hadamard`: Element-wise multiplication of two vectors.
* `filtered_gradient`: The final gradient after applying the Z-score mask.

## Main theorems

* `filtered_gradient_norm_sq_le`: Proves that the filter is an $L_2$ contraction.
* `z_score_nonempty`: Proves that the filter preserves at least one component
  when $z \le 1$.
-/

namespace LeanSharp

open BigOperators

variable {d : ℕ}

/-- The mean of a vector in `W = ℝ^d`. -/
noncomputable def vector_mean (g : W d) : ℝ :=
  (∑ i : Fin d, (WithLp.equiv 2 (Fin d → ℝ) g) i) / (d : ℝ)

/-- The variance of a vector in $W = ℝ^d$. -/
noncomputable def vector_variance (g : W d) : ℝ :=
  let μ := vector_mean g
  (∑ i : Fin d, ((WithLp.equiv 2 (Fin d → ℝ) g) i - μ)^2) / (d : ℝ)

/-- The standard deviation `σ` is the square root of the variance. -/
noncomputable def vector_std (g : W d) : ℝ :=
  Real.sqrt (vector_variance g)

@[simp]
lemma vector_mean_smul (k : ℝ) (g : W d) :
    vector_mean (k • g) = k * vector_mean g := by
  unfold vector_mean
  have h_smul (i : Fin d) :
    (WithLp.equiv 2 (Fin d → ℝ) (k • g)) i = k * (WithLp.equiv 2 (Fin d → ℝ) g) i := rfl
  simp only [h_smul, ← Finset.mul_sum]
  rw [mul_div_assoc]

@[simp]
lemma vector_variance_smul (k : ℝ) (g : W d) :
    vector_variance (k • g) = k^2 * vector_variance g := by
  unfold vector_variance
  simp only [vector_mean_smul]
  have h_inner (i : Fin d) : ((WithLp.equiv 2 (Fin d → ℝ) (k • g)) i - k * vector_mean g)^2 =
    k^2 * ((WithLp.equiv 2 (Fin d → ℝ) g) i - vector_mean g)^2 := by
    have : (WithLp.equiv 2 (Fin d → ℝ) (k • g)) i = k * (WithLp.equiv 2 (Fin d → ℝ) g) i := rfl
    rw [this, ← mul_sub, mul_pow]
  simp only [h_inner, ← Finset.mul_sum, mul_div_assoc]

@[simp]
lemma vector_std_smul {k : ℝ} (hk : 0 ≤ k) (g : W d) :
    vector_std (k • g) = k * vector_std g := by
  unfold vector_std
  rw [vector_variance_smul]
  have h_nonneg : 0 ≤ vector_variance g := by
    unfold vector_variance
    positivity
  rw [Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk]

/-- The Z-score Mask operator. Returns a new vector in `W`. -/
noncomputable def z_score_mask (g : W d) (z : ℝ) : W d :=
  let μ := vector_mean g
  let σ := vector_std g
  WithLp.equiv 2 (Fin d → ℝ) |>.symm fun i =>
    if |(WithLp.equiv 2 (Fin d → ℝ) g) i - μ| ≥ z * σ then 1 else 0

/-- Element-wise multiplication (Hadamard product) of vectors in $W$. -/
noncomputable def hadamard (a b : W d) : W d :=
  WithLp.equiv 2 (Fin d → ℝ) |>.symm fun i =>
    (WithLp.equiv 2 (Fin d → ℝ) a) i * (WithLp.equiv 2 (Fin d → ℝ) b) i

/-- The fully filtered gradient used in the parameter update. -/
noncomputable def filtered_gradient (g : W d) (z : ℝ) : W d :=
  hadamard g (z_score_mask g z)

/-- **Mask Contraction**: The L2 norm squared of the filtered gradient is bounded
by the original. -/
theorem filtered_gradient_norm_sq_le (g : W d) (z : ℝ) :
    ‖filtered_gradient g z‖^2 ≤ ‖g‖^2 := by
  have H1 : ‖filtered_gradient g z‖^2 = ∑ i : Fin d, ‖(filtered_gradient g z) i‖^2 := by
    exact EuclideanSpace.norm_sq_eq (filtered_gradient g z)
  have H2 : ‖g‖^2 = ∑ i : Fin d, ‖g i‖^2 := by
    exact EuclideanSpace.norm_sq_eq g
  rw [H1, H2]
  apply Finset.sum_le_sum
  intro i _
  unfold filtered_gradient hadamard z_score_mask
  simp only [WithLp.equiv_apply, Equiv.apply_symm_apply, Real.norm_eq_abs]
  have h_base : ‖(WithLp.equiv 2 (Fin d → ℝ) g) i *
      if |(WithLp.equiv 2 (Fin d → ℝ) g) i - vector_mean g|
        ≥ z * vector_std g then (1 : ℝ) else 0‖^2
    ≤ ‖(WithLp.equiv 2 (Fin d → ℝ) g) i‖^2 := by
    split_ifs with h_cond
    · simp only [mul_one, le_refl]
    · simp only [mul_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Real.norm_eq_abs, sq_abs]
      positivity
  exact h_base

/-- **Filtered Norm Bound**: The Z-score filter reduces or preserves the vector norm. -/
theorem filtered_norm_bound (g : W d) (z : ℝ) :
    ‖filtered_gradient g z‖ ≤ ‖g‖ := by
  have h_sq := filtered_gradient_norm_sq_le g z
  have h_sqrt := Real.sqrt_le_sqrt h_sq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h_sqrt
  exact h_sqrt

/-- **Mask Contraction**: The L2 norm squared variant of the bound. -/
theorem filtered_norm_bound_sq (g : W d) (z : ℝ) :
    ‖filtered_gradient g z‖^2 ≤ ‖g‖^2 := filtered_gradient_norm_sq_le g z

/-- **Filter Sparsity (Non-emptiness)**: For z ≤ 1, the filter always preserves at least
one component of the gradient. -/
theorem z_score_nonempty [Fact (0 < d)] (g : W d) {z : ℝ} (hz_le : z ≤ 1) :
    ∃ i : Fin d, (WithLp.equiv 2 (Fin d → ℝ) (z_score_mask g z)) i = 1 := by
  let μ := vector_mean g
  let σ := vector_std g
  haveI : 0 < d := Fact.out
  by_cases hσ : σ = 0
  · -- Case σ = 0: All are kept.
    use ⟨0, ‹0 < d›⟩
    simp [z_score_mask, σ, hσ]
  · -- Case σ > 0: Contradiction if all are zeroed.
    by_contra h
    push_neg at h
    -- If (mask g z) i ≠ 1, then it must be 0.
    have h_abs : ∀ i : Fin d, |(WithLp.equiv 2 (Fin d → ℝ) g) i - μ| < z * σ := by
      intro i
      have hi := h i
      unfold z_score_mask at hi
      simp only [WithLp.equiv_apply, Equiv.apply_symm_apply] at hi
      split_ifs at hi with h_cond
      · contradiction
      · push_neg at h_cond; exact h_cond
    -- Since z ≤ 1, |g i - μ| < σ.
    have h_sq : ∀ i : Fin d, ((WithLp.equiv 2 (Fin d → ℝ) g) i - μ)^2 < σ^2 := by
      intro i
      have hlt := h_abs i
      have h_nonneg : 0 ≤ σ := Real.sqrt_nonneg _
      have hsz : z * σ ≤ σ := mul_le_of_le_one_left h_nonneg hz_le
      have h_lt : |(WithLp.equiv 2 (Fin d → ℝ) g) i - μ| < σ := hlt.trans_le hsz
      rw [sq_lt_sq, abs_of_nonneg h_nonneg]
      exact h_lt
    -- Summing gives Σ (g_i - μ)² < d * σ².
    have h_sum : (∑ i : Fin d, ((WithLp.equiv 2 (Fin d → ℝ) g) i - μ)^2) < d * σ^2 := by
      haveI : Nonempty (Fin d) := ⟨⟨0, ‹0 < d›⟩⟩
      calc (∑ i : Fin d, ((WithLp.equiv 2 (Fin d → ℝ) g) i - μ)^2)
          < (∑ i : Fin d, σ^2) :=
            Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => h_sq i)
        _ = d * σ^2 := by simp
    -- But Σ |g i - μ|² = d * σ² by definition.
    have h_def : (∑ i : Fin d, ((WithLp.equiv 2 (Fin d → ℝ) g) i - μ)^2) = d * σ^2 := by
      have h_d_pos : 0 < (d : ℝ) := by positivity
      have h_var_pos : 0 ≤ vector_variance g := by unfold vector_variance; positivity
      have h_sq_std : (Real.sqrt (vector_variance g))^2 = vector_variance g :=
        Real.sq_sqrt h_var_pos
      unfold σ at hσ h_sq_std ⊢
      rw [vector_std, h_sq_std]
      unfold vector_variance
      dsimp
      have : (d : ℝ) ≠ 0 := by positivity
      rw [mul_div_cancel₀ _ ‹_›]
    linarith

end LeanSharp
