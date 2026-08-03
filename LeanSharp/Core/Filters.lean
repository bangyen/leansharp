/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Objective
import LeanSharp.Core.Stats
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Z-Score Gradient Filtering

This module formalizes the statistical filtering of gradient tensors using
Z-score masking.

## Main definitions

* `zScoreMask`: A boolean-valued vector in $\{0, 1\}^d$ indicating components
  within the Z-score threshold.
* `hadamard`: Element-wise multiplication of two vectors.
* `filteredGradient`: The final gradient after applying the Z-score mask.

## Main theorems

* `norm_filtered_gradient_le`: Direct corollary of the $L_2$ contraction, as a norm-level interface.
* `norm_sq_filtered_gradient_le`: Proves that the filter is an $L_2$ contraction.
* `zscore_mask_nonempty`: Proves that the filter preserves at least one component
  when $z \le 1$.
* `filtered_gradient_eq_self_of_std_zero`: Proves that constant gradients are
  preserved by the filter.
* `zscore_mask_idempotent`: Proves the mask is idempotent under Hadamard product.
-/

namespace LeanSharp

open BigOperators

variable {ι : Type*} [Fintype ι]

/-- The Z-score Mask operator. Returns a new vector in `W` with `1` on components
    within the Z-score threshold of the mean (the inliers) and `0` on outliers. -/
noncomputable def zScoreMask (g : W ι) (z : ℝ) : W ι :=
  let μ := vectorMean g
  let σ := vectorStd g
  WithLp.equiv 2 (ι → ℝ) |>.symm fun i =>
    if |(WithLp.equiv 2 (ι → ℝ) g) i - μ| ≤ z * σ then 1 else 0

/-- Element-wise multiplication (Hadamard product) of vectors in $W$. -/
noncomputable def hadamard (a b : W ι) : W ι :=
  WithLp.equiv 2 (ι → ℝ) |>.symm fun i =>
    (WithLp.equiv 2 (ι → ℝ) a) i * (WithLp.equiv 2 (ι → ℝ) b) i

/-- The fully filtered gradient used in the parameter update. -/
noncomputable def filteredGradient (g : W ι) (z : ℝ) : W ι :=
  hadamard g (zScoreMask g z)

/-- **Mask Contraction**: The L2 norm squared of the filtered gradient is bounded
by the original. -/
theorem norm_sq_filtered_gradient_le (g : W ι) (z : ℝ) :
    ‖filteredGradient g z‖^2 ≤ ‖g‖^2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  unfold filteredGradient hadamard zScoreMask
  rw [WithLp.equiv_apply, Equiv.apply_symm_apply]
  dsimp only [ge_iff_le, WithLp.equiv_symm_apply, Real.norm_eq_abs]
  split_ifs
  · rw [mul_one, sq_abs]
  · simp only [
      mul_zero,
      ne_eq,
      OfNat.ofNat_ne_zero,
      not_false_eq_true,
      zero_pow,
      sq_abs
    ]
    positivity

/-- **Filtered Norm Bound (API convenience)**: Direct corollary of
`norm_sq_filtered_gradient_le`; kept as a simpler norm-level interface. -/
theorem norm_filtered_gradient_le (g : W ι) (z : ℝ) :
    ‖filteredGradient g z‖ ≤ ‖g‖ := by
  have h_sq := norm_sq_filtered_gradient_le g z
  have h_sqrt := Real.sqrt_le_sqrt h_sq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h_sqrt
  exact h_sqrt

/-- **Non-emptiness Contradiction**: The core contradiction step for Z-score non-emptiness.
If all components were filtered out (each beyond the threshold), the empirical variance
would be larger than itself. -/
private lemma zscore_mask_nonempty_contradiction [Nonempty ι] (g : W ι) (z : ℝ) (hz_ge : 1 ≤ z)
    (h_filtered : ∀ i : ι, (WithLp.equiv 2 (ι → ℝ) (zScoreMask g z)) i = 0) :
    False := by
  haveI : Nonempty ι := inferInstance
  have h_sq : ∀ i : ι, (vectorStd g)^2 <
      ((WithLp.equiv 2 (ι → ℝ) g) i - vectorMean g)^2 := by
    intro i
    have hi := h_filtered i
    unfold zScoreMask at hi
    rw [Equiv.apply_symm_apply] at hi
    split_ifs at hi with h_cond
    · norm_num at hi
    · have h_abs : z * vectorStd g < |(WithLp.equiv 2 (ι → ℝ) g) i - vectorMean g| := by
        exact not_le.mp h_cond
      have h_nonneg : 0 ≤ vectorStd g := Real.sqrt_nonneg _
      have hsz : vectorStd g ≤ z * vectorStd g := le_mul_of_one_le_left h_nonneg hz_ge
      have h_lt : vectorStd g < |(WithLp.equiv 2 (ι → ℝ) g) i - vectorMean g| :=
        hsz.trans_lt h_abs
      rw [sq_lt_sq, abs_of_nonneg h_nonneg]
      exact h_lt
  have h_sum_lt : (Fintype.card ι : ℝ) * (vectorStd g)^2 <
      (∑ i : ι, ((WithLp.equiv 2 (ι → ℝ) g) i - vectorMean g)^2) := by
    calc (Fintype.card ι : ℝ) * (vectorStd g)^2
        = ∑ i : ι, (vectorStd g)^2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ < (∑ i : ι, ((WithLp.equiv 2 (ι → ℝ) g) i - vectorMean g)^2) :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => h_sq i)
  have h_sum_eq : (∑ i : ι, ((WithLp.equiv 2 (ι → ℝ) g) i - vectorMean g)^2) =
      (Fintype.card ι : ℝ) * (vectorStd g)^2 := by
    have h_var_pos : 0 ≤ vectorVariance g := by unfold vectorVariance; positivity
    rw [vectorStd, Real.sq_sqrt h_var_pos, vectorVariance]
    have hd : (Fintype.card ι : ℝ) ≠ 0 := by
      have h_pos : 0 < Fintype.card ι := Fintype.card_pos
      positivity
    field_simp [hd]
  linarith

/-- **Filter Sparsity (Non-emptiness)**: For z ≥ 1, the filter always preserves at least
one component of the gradient. -/
theorem zscore_mask_nonempty [Nonempty ι] (g : W ι) {z : ℝ} (hz_ge : 1 ≤ z) :
    ∃ i : ι, (WithLp.equiv 2 (ι → ℝ) (zScoreMask g z)) i = 1 := by
  let σ := vectorStd g
  haveI : 0 < Fintype.card ι := Fintype.card_pos
  by_cases hσ : σ = 0
  · use Classical.arbitrary ι
    have hstd : vectorStd g = 0 := by simpa only [σ] using hσ
    have h_var : vectorVariance g = 0 := by
      have hsqrt : Real.sqrt (vectorVariance g) = 0 := by simpa only [vectorStd] using hstd
      exact (Real.sqrt_eq_zero (by unfold vectorVariance; positivity)).mp hsqrt
    have h_eq : ∀ i : ι, (WithLp.equiv 2 (ι → ℝ) g) i = vectorMean g :=
      eq_mean_of_vectorVariance_eq_zero g h_var
    simp only [zScoreMask, WithLp.equiv_apply, h_eq, hstd, mul_zero, ↓reduceIte,
      WithLp.equiv_symm_apply, sub_self, abs_zero, le_refl]
  · by_contra h
    push_neg at h
    refine zscore_mask_nonempty_contradiction g z hz_ge (fun i => ?_)
    have hi := h i
    unfold zScoreMask at hi ⊢
    rw [Equiv.apply_symm_apply] at hi ⊢
    split_ifs with h_cond <;> simp only [
      ↓reduceIte,
      ne_eq,
      not_true_eq_false,
      h_cond
    ] at hi ⊢

/-- **Zero Signal Stability**: If all components of the gradient are identical (zero variance),
the filter preserves the entire gradient because every component is exactly at the mean. -/
theorem filtered_gradient_eq_self_of_std_zero [Nonempty ι] (g : W ι) (z : ℝ)
    (h_std : vectorStd g = 0) :
    filteredGradient g z = g := by
  have h_var : vectorVariance g = 0 := by
    have hsqrt : Real.sqrt (vectorVariance g) = 0 := by simpa only [vectorStd] using h_std
    exact (Real.sqrt_eq_zero (by unfold vectorVariance; positivity)).mp hsqrt
  have h_eq : ∀ i : ι, (WithLp.equiv 2 (ι → ℝ) g) i = vectorMean g :=
    eq_mean_of_vectorVariance_eq_zero g h_var
  unfold filteredGradient hadamard zScoreMask
  apply (WithLp.equiv 2 (ι → ℝ)).injective
  ext i
  simp only [h_std, h_eq, mul_zero, sub_self, abs_zero, ↓reduceIte, le_refl,
    Equiv.apply_symm_apply, mul_one]

/-- **Mask Idempotency**: The Z-score mask is its own Hadamard product
    (since its components are 0 or 1). -/
theorem zscore_mask_idempotent (g : W ι) (z : ℝ) :
    hadamard (zScoreMask g z) (zScoreMask g z) = zScoreMask g z := by
  unfold hadamard zScoreMask
  apply (WithLp.equiv 2 (ι → ℝ)).injective
  ext i
  simp only [Equiv.apply_symm_apply]
  split_ifs <;> simp only [mul_one, mul_zero]

/-- The update step for Sharpness-Aware Minimization with Z-score filtering. -/
noncomputable def samZSharpUpdate (L : W ι → ℝ) (w : W ι) (η ρ z : ℝ) : W ι :=
  w - η • filteredGradient (gradient L (w + samPerturbation L w ρ)) z

end LeanSharp
