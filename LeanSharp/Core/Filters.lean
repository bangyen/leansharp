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

variable {ι : Type*} [Fintype ι]

/-- The Z-score Mask operator. Returns a new vector in `W`. -/
noncomputable def z_score_mask (g : W ι) (z : ℝ) : W ι :=
  let μ := vector_mean g
  let σ := vector_std g
  WithLp.equiv 2 (ι → ℝ) |>.symm fun i =>
    if |(WithLp.equiv 2 (ι → ℝ) g) i - μ| ≥ z * σ then 1 else 0

/-- Element-wise multiplication (Hadamard product) of vectors in $W$. -/
noncomputable def hadamard (a b : W ι) : W ι :=
  WithLp.equiv 2 (ι → ℝ) |>.symm fun i =>
    (WithLp.equiv 2 (ι → ℝ) a) i * (WithLp.equiv 2 (ι → ℝ) b) i

/-- The fully filtered gradient used in the parameter update. -/
noncomputable def filtered_gradient (g : W ι) (z : ℝ) : W ι :=
  hadamard g (z_score_mask g z)

/-- **Mask Contraction**: The L2 norm squared of the filtered gradient is bounded
by the original. -/
theorem filtered_gradient_norm_sq_le (g : W ι) (z : ℝ) :
    ‖filtered_gradient g z‖^2 ≤ ‖g‖^2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  unfold filtered_gradient hadamard z_score_mask
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

/-- **Filtered Norm Bound**: The Z-score filter reduces or preserves the vector norm. -/
theorem filtered_norm_bound (g : W ι) (z : ℝ) :
    ‖filtered_gradient g z‖ ≤ ‖g‖ := by
  have h_sq := filtered_gradient_norm_sq_le g z
  have h_sqrt := Real.sqrt_le_sqrt h_sq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h_sqrt
  exact h_sqrt

/-- **Non-emptiness Contradiction**: The core contradiction step for Z-score non-emptiness.
If all components were filtered out, the empirical variance would be less than itself. -/
private lemma z_score_nonempty_contradiction [Nonempty ι] (g : W ι) (z : ℝ) (hz_le : z ≤ 1)
    (h_filtered : ∀ i : ι, (WithLp.equiv 2 (ι → ℝ) (z_score_mask g z)) i = 0) :
    False := by
  haveI : Nonempty ι := inferInstance
  have h_sq : ∀ i : ι, ((WithLp.equiv 2 (ι → ℝ) g) i - vector_mean g)^2 <
      (vector_std g)^2 := by
    intro i
    have hi := h_filtered i
    unfold z_score_mask at hi
    rw [Equiv.apply_symm_apply] at hi
    split_ifs at hi with h_cond
    · norm_num at hi
    · have h_abs := not_le.mp h_cond
      have h_nonneg : 0 ≤ vector_std g := Real.sqrt_nonneg _
      have hsz : z * vector_std g ≤ vector_std g := mul_le_of_le_one_left h_nonneg hz_le
      have h_lt : |(WithLp.equiv 2 (ι → ℝ) g) i - vector_mean g| < vector_std g :=
        h_abs.trans_le hsz
      rw [sq_lt_sq, abs_of_nonneg h_nonneg]
      exact h_lt
  -- Step 2: Use the Variance Sum Equality and Sum of Squares Bound (inlined)
  have h_sum_lt : (∑ i : ι, ((WithLp.equiv 2 (ι → ℝ) g) i - vector_mean g)^2) <
      (Fintype.card ι : ℝ) * (vector_std g)^2 := by
    calc (∑ i : ι, ((WithLp.equiv 2 (ι → ℝ) g) i - vector_mean g)^2)
        < (∑ i : ι, (vector_std g)^2) :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => h_sq i)
      _ = (Fintype.card ι : ℝ) * (vector_std g)^2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_sum_eq : (∑ i : ι, ((WithLp.equiv 2 (ι → ℝ) g) i - vector_mean g)^2) =
      (Fintype.card ι : ℝ) * (vector_std g)^2 := by
    have h_var_pos : 0 ≤ vector_variance g := by unfold vector_variance; positivity
    rw [vector_std, Real.sq_sqrt h_var_pos, vector_variance]
    have hd : (Fintype.card ι : ℝ) ≠ 0 := by
      have h_pos : 0 < Fintype.card ι := Fintype.card_pos
      positivity
    field_simp [hd]
  linarith

/-- **Filter Sparsity (Non-emptiness)**: For z ≤ 1, the filter always preserves at least
one component of the gradient. -/
theorem z_score_nonempty [Nonempty ι] (g : W ι) {z : ℝ} (hz_le : z ≤ 1) :
    ∃ i : ι, (WithLp.equiv 2 (ι → ℝ) (z_score_mask g z)) i = 1 := by
  let σ := vector_std g
  haveI : 0 < Fintype.card ι := Fintype.card_pos
  by_cases hσ : σ = 0
  · use Classical.arbitrary ι; simp only [
      z_score_mask,
      WithLp.equiv_apply,
      hσ,
      mul_zero,
      ge_iff_le,
      abs_nonneg,
      ↓reduceIte,
      WithLp.equiv_symm_apply,
      σ
    ]
  · by_contra h
    push_neg at h
    refine z_score_nonempty_contradiction g z hz_le (fun i => ?_)
    have hi := h i
    unfold z_score_mask at hi ⊢
    rw [Equiv.apply_symm_apply] at hi ⊢
    split_ifs with h_cond <;> simp only [
      ge_iff_le,
      ↓reduceIte,
      ne_eq,
      not_true_eq_false,
      h_cond
    ] at hi ⊢

/-- The update step for Sharpness-Aware Minimization with Z-score filtering. -/
noncomputable def sam_zsharp_update (L : W ι → ℝ) (w : W ι) (η ρ z : ℝ) : W ι :=
  w - η • filtered_gradient (gradient L (w + sam_perturbation L w ρ)) z

end LeanSharp
