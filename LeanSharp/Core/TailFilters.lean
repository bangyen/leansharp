/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters

/-!
# Paper-Faithful Z-Score Tail Filtering

This module formalizes the gradient filter of *Sharpness-Aware Minimization with
Z-Score Gradient Filtering* (arXiv:2505.02369), which keeps the components whose
absolute Z-score is **largest**:

$$m_j = 1 \iff |\Omega(\nabla L(w))_j| > q,$$

amplifying the directions that "stand out most compared to the average of the
layer". This is the exact complement of `zScoreMask`, which keeps the components
*within* the threshold in order to suppress outliers.

Both filters are retained. The inlier filter is what the robustness development
is stated over; this tail filter is what the ZSharp ascent step uses. The
threshold here is still the fixed multiplier $z\sigma$ rather than the paper's
percentile $q_{Q_p}$ — that divergence is tracked separately.

## Main definitions

* `zScoreTailMask`: the complement of `zScoreMask`, keeping components more than
  $z\sigma$ from the mean.
* `tailFilteredGradient`: the gradient after applying the tail mask.

## Main theorems

* `zScoreTailMask_add_zScoreMask`: the two masks partition the coordinates.
* `tail_filtered_add_filtered`: the two filters decompose the gradient exactly.
* `norm_sq_tail_filtered_gradient_le`: the tail filter is an $L_2$ contraction.
* `norm_tail_filtered_gradient_le`: norm-level form of the contraction.
* `zScoreTailMask_idempotent`: the tail mask is idempotent under Hadamard product.
* `tail_filtered_gradient_eq_zero_of_std_zero`: constant gradients are annihilated.
-/

namespace LeanSharp

open BigOperators

variable {ι : Type*} [Fintype ι]

/-- The Z-score tail mask: `1` on components further than `z * σ` from the mean (the
outliers) and `0` elsewhere. This is the paper's mask, and the exact complement of
`zScoreMask`. -/
noncomputable def zScoreTailMask (g : W ι) (z : ℝ) : W ι :=
  let μ := vectorMean g
  let σ := vectorStd g
  WithLp.equiv 2 (ι → ℝ) |>.symm fun i =>
    if |(WithLp.equiv 2 (ι → ℝ) g) i - μ| ≤ z * σ then 0 else 1

/-- The gradient filtered by the tail mask: the paper's `∇L(w)_Ω`. -/
noncomputable def tailFilteredGradient (g : W ι) (z : ℝ) : W ι :=
  hadamard g (zScoreTailMask g z)

/-- **Mask Partition**: the tail mask and the inlier mask sum to the all-ones vector,
so together they partition the coordinates. -/
theorem zScoreTailMask_add_zScoreMask (g : W ι) (z : ℝ) :
    zScoreTailMask g z + zScoreMask g z =
      (WithLp.equiv 2 (ι → ℝ)).symm (fun _ => 1) := by
  apply (WithLp.equiv 2 (ι → ℝ)).injective
  ext i
  unfold zScoreTailMask zScoreMask
  change (if |g.ofLp i - vectorMean g| ≤ z * vectorStd g then (0:ℝ) else 1) +
      (if |g.ofLp i - vectorMean g| ≤ z * vectorStd g then (1:ℝ) else 0) = 1
  split_ifs <;> norm_num

/-- **Filter Decomposition**: filtering by the tail and by the inliers splits the
gradient exactly, `∇L(w)_Ω + filteredGradient = ∇L(w)`. -/
theorem tail_filtered_add_filtered (g : W ι) (z : ℝ) :
    tailFilteredGradient g z + filteredGradient g z = g := by
  apply (WithLp.equiv 2 (ι → ℝ)).injective
  ext i
  unfold tailFilteredGradient filteredGradient hadamard zScoreTailMask zScoreMask
  change g.ofLp i * (if |g.ofLp i - vectorMean g| ≤ z * vectorStd g then 0 else 1) +
      g.ofLp i * (if |g.ofLp i - vectorMean g| ≤ z * vectorStd g then 1 else 0) = g.ofLp i
  split_ifs <;> ring

/-- **Tail Mask Contraction**: the tail filter never increases the squared norm. -/
theorem norm_sq_tail_filtered_gradient_le (g : W ι) (z : ℝ) :
    ‖tailFilteredGradient g z‖^2 ≤ ‖g‖^2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  unfold tailFilteredGradient hadamard zScoreTailMask
  rw [WithLp.equiv_apply, Equiv.apply_symm_apply]
  dsimp only [ge_iff_le, WithLp.equiv_symm_apply, Real.norm_eq_abs]
  split_ifs
  · simp only [
      mul_zero,
      ne_eq,
      OfNat.ofNat_ne_zero,
      not_false_eq_true,
      zero_pow,
      sq_abs
    ]
    positivity
  · rw [mul_one, sq_abs]

/-- **Tail Filtered Norm Bound**: norm-level form of the contraction. -/
theorem norm_tail_filtered_gradient_le (g : W ι) (z : ℝ) :
    ‖tailFilteredGradient g z‖ ≤ ‖g‖ := by
  have h_sq := norm_sq_tail_filtered_gradient_le g z
  have h_sqrt := Real.sqrt_le_sqrt h_sq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h_sqrt
  exact h_sqrt

/-- **Tail Mask Idempotency**: the tail mask is its own Hadamard product. -/
theorem zScoreTailMask_idempotent (g : W ι) (z : ℝ) :
    hadamard (zScoreTailMask g z) (zScoreTailMask g z) = zScoreTailMask g z := by
  unfold hadamard zScoreTailMask
  apply (WithLp.equiv 2 (ι → ℝ)).injective
  ext i
  simp only [Equiv.apply_symm_apply]
  split_ifs <;> simp only [mul_one, mul_zero]

/-- **Zero Signal Annihilation**: a constant gradient has no outliers, so the tail
filter zeroes it entirely. This is the exact dual of
`filtered_gradient_eq_self_of_std_zero`, and it is what makes the fallback branch of
`zsharpPerturbation` reachable. -/
theorem tail_filtered_gradient_eq_zero_of_std_zero [Nonempty ι] (g : W ι) (z : ℝ)
    (h_std : vectorStd g = 0) :
    tailFilteredGradient g z = 0 := by
  have h_var : vectorVariance g = 0 := by
    have hsqrt : Real.sqrt (vectorVariance g) = 0 := by simpa only [vectorStd] using h_std
    exact (Real.sqrt_eq_zero (by unfold vectorVariance; positivity)).mp hsqrt
  have h_eq : ∀ i : ι, (WithLp.equiv 2 (ι → ℝ) g) i = vectorMean g :=
    eq_mean_of_vectorVariance_eq_zero g h_var
  unfold tailFilteredGradient hadamard zScoreTailMask
  apply (WithLp.equiv 2 (ι → ℝ)).injective
  ext i
  simp only [h_std, h_eq, mul_zero, sub_self, abs_zero, ↓reduceIte, le_refl,
    Equiv.apply_symm_apply, mul_zero]
  rfl

end LeanSharp
