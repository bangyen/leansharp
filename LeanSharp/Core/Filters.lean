/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Sam
import LeanSharp.Core.Stats
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Z-Score Gradient Filtering

This module formalizes the statistical filtering of gradient tensors using
Z-score masking.

## Main definitions

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
  simp_rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  unfold filtered_gradient hadamard z_score_mask
  simp only [WithLp.equiv_apply, Equiv.apply_symm_apply]
  dsimp
  split_ifs
  · simp
  · simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sq_abs]
    positivity

/-- **Filtered Norm Bound**: The Z-score filter reduces or preserves the vector norm. -/
theorem filtered_norm_bound (g : W d) (z : ℝ) :
    ‖filtered_gradient g z‖ ≤ ‖g‖ := by
  have h_sq := filtered_gradient_norm_sq_le g z
  have h_sqrt := Real.sqrt_le_sqrt h_sq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h_sqrt
  exact h_sqrt


/-- **Variance Sum Equality**: The sum of squared deviations from the mean is equal to
the dimension times the variance (square of standard deviation). -/
private lemma sum_sq_deviation_eq_d_var (g : W d) :
    (∑ i : Fin d, ((WithLp.equiv 2 (Fin d → ℝ) g) i - vector_mean g)^2) = d * (vector_std g)^2 := by
  have h_var_pos : 0 ≤ vector_variance g := by unfold vector_variance; positivity
  rw [vector_std, Real.sq_sqrt h_var_pos, vector_variance]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · field_simp [hd.ne']

/-- **Sum of Squares Bound**: If every squared deviation is strictly less than σ²,
the total sum is strictly less than d * σ². -/
private lemma sum_sq_deviation_lt_d_var {σ : ℝ}
    (h_lt : ∀ i : Fin d, ((WithLp.equiv 2 (Fin d → ℝ) g) i - μ)^2 < σ^2)
    [Nonempty (Fin d)] :
    (∑ i : Fin d, ((WithLp.equiv 2 (Fin d → ℝ) g) i - μ)^2) < d * σ^2 := by
  calc (∑ i : Fin d, ((WithLp.equiv 2 (Fin d → ℝ) g) i - μ)^2)
      < (∑ i : Fin d, σ^2) :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => h_lt i)
    _ = d * σ^2 := by simp

/-- **Squared Deviation Bound**: If a component's Z-score is less than or equal to $z \le 1$,
its squared deviation is strictly less than the variance (provided variance is non-zero). -/
private lemma sq_deviation_lt_std_sq_of_z_le_one (g : W d) (i : Fin d) (z : ℝ)
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
private lemma z_score_nonempty_contradiction [Fact (0 < d)] (g : W d) (z : ℝ) (hz_le : z ≤ 1)
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
