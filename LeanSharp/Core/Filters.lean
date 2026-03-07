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

/-- **Binary Mask Norm Bound**: Multiplying a scalar by 0 or 1 does not increase its
norm squared. -/
lemma norm_sq_mul_binary_le (x : ℝ) (P : Prop) [Decidable P] :
    ‖x * (if P then (1 : ℝ) else 0)‖^2 ≤ ‖x‖^2 := by
  split_ifs
  · simp
  · simp only [mul_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Real.norm_eq_abs, sq_abs]
    positivity

/-- **Mask Contraction**: The L2 norm squared of the filtered gradient is bounded
by the original. -/
theorem filtered_gradient_norm_sq_le (g : W d) (z : ℝ) :
    ‖filtered_gradient g z‖^2 ≤ ‖g‖^2 := by
  simp_rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  unfold filtered_gradient hadamard z_score_mask
  simp only [WithLp.equiv_apply, Equiv.apply_symm_apply]
  apply norm_sq_mul_binary_le

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

/-- **Variance Sum Equality**: The sum of squared deviations from the mean is equal to
the dimension times the variance (square of standard deviation). -/
lemma sum_sq_deviation_eq_d_var (g : W d) :
    (∑ i : Fin d, ((WithLp.equiv 2 (Fin d → ℝ) g) i - vector_mean g)^2) = d * (vector_std g)^2 := by
  have h_var_pos : 0 ≤ vector_variance g := by unfold vector_variance; positivity
  have h_sq_std : (vector_std g)^2 = vector_variance g := Real.sq_sqrt h_var_pos
  rw [h_sq_std]
  unfold vector_variance
  by_cases hd : (d : ℝ) = 0
  · have : d = 0 := by exact_mod_cast hd
    subst this
    simp
  · rw [mul_div_cancel₀ _ hd]

/-- **Sum of Squares Bound**: If every squared deviation is strictly less than σ²,
the total sum is strictly less than d * σ². -/
lemma sum_sq_deviation_lt_d_var {σ : ℝ}
    (h_lt : ∀ i : Fin d, ((WithLp.equiv 2 (Fin d → ℝ) g) i - μ)^2 < σ^2)
    [Nonempty (Fin d)] :
    (∑ i : Fin d, ((WithLp.equiv 2 (Fin d → ℝ) g) i - μ)^2) < d * σ^2 := by
  calc (∑ i : Fin d, ((WithLp.equiv 2 (Fin d → ℝ) g) i - μ)^2)
      < (∑ i : Fin d, σ^2) :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => h_lt i)
    _ = d * σ^2 := by simp

/-- **Squared Deviation Bound**: If a component's Z-score is less than or equal to $z \le 1$,
its squared deviation is strictly less than the variance (provided variance is non-zero). -/
lemma sq_deviation_lt_std_sq_of_z_le_one (g : W d) (i : Fin d) (z : ℝ)
    (hz_le : z ≤ 1) (h_abs : |(WithLp.equiv 2 (Fin d → ℝ) g) i - vector_mean g| <
      z * vector_std g) :
    ((WithLp.equiv 2 (Fin d → ℝ) g) i - vector_mean g)^2 < (vector_std g)^2 := by
  have h_nonneg : 0 ≤ vector_std g := Real.sqrt_nonneg _
  have hsz : z * vector_std g ≤ vector_std g := mul_le_of_le_one_left h_nonneg hz_le
  have h_lt : |(WithLp.equiv 2 (Fin d → ℝ) g) i - vector_mean g| < vector_std g :=
    h_abs.trans_le hsz
  rw [sq_lt_sq, abs_of_nonneg h_nonneg]
  exact h_lt

/-- **Non-emptiness Contradiction**: The core contradiction step for Z-score non-emptiness.
If all components were filtered out, the empirical variance would be less than itself. -/
lemma z_score_nonempty_contradiction [Fact (0 < d)] (g : W d) (z : ℝ) (hz_le : z ≤ 1)
    (h_filtered : ∀ i : Fin d, (WithLp.equiv 2 (Fin d → ℝ) (z_score_mask g z)) i = 0) :
    False := by
  haveI : Nonempty (Fin d) := ⟨⟨0, Fact.out⟩⟩
  have h_sq : ∀ i : Fin d, ((WithLp.equiv 2 (Fin d → ℝ) g) i - vector_mean g)^2 <
      (vector_std g)^2 := by
    intro i
    have hi := h_filtered i
    unfold z_score_mask at hi
    simp only [WithLp.equiv_apply, Equiv.apply_symm_apply] at hi
    split_ifs at hi with h_cond
    · norm_num at hi
    · exact sq_deviation_lt_std_sq_of_z_le_one g i z hz_le (not_le.mp h_cond)
  linarith [sum_sq_deviation_lt_d_var h_sq, sum_sq_deviation_eq_d_var g]

/-- **Filter Sparsity (Non-emptiness)**: For z ≤ 1, the filter always preserves at least
one component of the gradient. -/
theorem z_score_nonempty [Fact (0 < d)] (g : W d) {z : ℝ} (hz_le : z ≤ 1) :
    ∃ i : Fin d, (WithLp.equiv 2 (Fin d → ℝ) (z_score_mask g z)) i = 1 := by
  let σ := vector_std g
  haveI : 0 < d := Fact.out
  by_cases hσ : σ = 0
  · use ⟨0, ‹0 < d›⟩; simp [z_score_mask, σ, hσ]
  · by_contra h
    push_neg at h
    refine z_score_nonempty_contradiction g z hz_le (fun i => ?_)
    have hi := h i
    unfold z_score_mask at hi ⊢
    simp only [WithLp.equiv_apply, Equiv.apply_symm_apply] at hi ⊢
    split_ifs with h_cond <;> simp [*] at hi ⊢

end LeanSharp
