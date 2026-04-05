/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Core.Stats
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
/-!
# Concentration Inequalities for W Vectors

This module develops discrete concentration bounds (e.g., Chebyshev)
for the empirical statistics of vectors in `W ι`.

As we scale up the dimension $|ι| \to \infty$, these inequalities provide
the non-asymptotic bounds required to prove the stability properties
of Z-score filtering without relying on specific distributional
assumptions (thus acting as our substitute for a Central Limit Theorem).

## Main Definitions

* `zScoreTails`: The subset of indices falling outside the Z-score threshold.

## Main Theorems

* `chebyshev_vector`: Discrete version of Chebyshev's inequality for vector components.
-/
namespace LeanSharp
open Finset BigOperators Real
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The subset of indices that fall in the tail, defined by the Z-score threshold.
    These are the components KEPT by `zScoreMask` when $z > 0$. -/
noncomputable def zScoreTails (g : W ι) (z : ℝ) : Finset ι :=
  univ.filter fun i => |(WithLp.equiv 2 (ι → ℝ) g) i - vectorMean g| ≥ z * vectorStd g

/-- **Discrete Chebyshev's Inequality for Vectors**:
For any $z > 0$, the fraction of coordinates falling in the $z$-standard
deviation tail is bounded by $1/z^2$ when variance is non-zero.
This guarantees the sparsity of the Z-score filter for large z. -/
theorem chebyshev_vector (g : W ι) {z : ℝ} (hz : 0 < z) (hvar : vectorVariance g > 0) :
    ((zScoreTails g z).card : ℝ) / (Fintype.card ι : ℝ) ≤ 1 / z^2 := by
  let μ := vectorMean g
  let σ := vectorStd g
  let σ2 := vectorVariance g
  let S := zScoreTails g z
  let r := (WithLp.equiv 2 (ι → ℝ) g)
  have h_var : σ2 = (∑ i : ι, (r i - μ)^2) / (Fintype.card ι : ℝ) := rfl
  have h_card_pos : (Fintype.card ι : ℝ) > 0 := by positivity
  have h_sum_ge : (S.card : ℝ) * (z * σ)^2 ≤ ∑ i : ι, (r i - μ)^2 := by
    calc
      (S.card : ℝ) * (z * σ)^2 = ∑ i ∈ S, (z * σ)^2 := by
        rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ S, (r i - μ)^2 := by
        apply sum_le_sum
        intro i hi
        have hi_mem := mem_filter.mp hi
        have h_abs : z * σ ≤ |r i - μ| := hi_mem.2
        have hz_pos : 0 ≤ z * σ := mul_nonneg (le_of_lt hz) (Real.sqrt_nonneg _)
        have h_abs_ineq : |z * σ| ≤ |r i - μ| := by rwa [abs_of_nonneg hz_pos]
        exact sq_le_sq.mpr h_abs_ineq
      _ ≤ ∑ i : ι, (r i - μ)^2 := by
        apply sum_le_univ_sum_of_nonneg
        intro i
        exact sq_nonneg (r i - μ)
  have hd : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt h_card_pos
  have h_var_rearranged : ∑ i : ι, (r i - μ)^2 = σ2 * (Fintype.card ι : ℝ) := by
    have h_div := div_mul_cancel₀ (∑ i : ι, (r i - μ)^2) hd
    rw [← h_var] at h_div
    exact h_div.symm
  have hzsq : (z * σ)^2 = z^2 * σ2 := by
    have h_std : σ^2 = σ2 := Real.sq_sqrt (vectorVariance_nonneg g)
    calc (z * σ)^2 = z^2 * σ^2 := mul_pow z σ 2
    _ = z^2 * σ2 := by rw [h_std]
  rw [h_var_rearranged, hzsq] at h_sum_ge
  -- h_sum_ge: S.card * z^2 * σ2 ≤ σ2 * card
  -- Divide by σ2 and card, multiply by 1/z^2
  have h_div_var : (S.card : ℝ) * z^2 ≤ (Fintype.card ι : ℝ) := by
    have h_rhs_comm : σ2 * (Fintype.card ι : ℝ) = (Fintype.card ι : ℝ) * σ2 := mul_comm _ _
    rw [h_rhs_comm] at h_sum_ge
    have h_assoc : (S.card : ℝ) * (z^2 * σ2) = ((S.card : ℝ) * z^2) * σ2 := (mul_assoc _ _ _).symm
    rw [h_assoc] at h_sum_ge
    exact le_of_mul_le_mul_right h_sum_ge hvar
  -- Rearrange to get S.card / card ≤ 1 / z^2
  have hz2_pos : z^2 > 0 := sq_pos_of_pos hz
  have h_div_card : (S.card : ℝ) / (Fintype.card ι : ℝ) * z^2 ≤ 1 := by
    rw [div_mul_eq_mul_div]
    exact (div_le_one h_card_pos).mpr h_div_var
  calc
    ((S.card : ℝ) / (Fintype.card ι : ℝ)) = ((S.card : ℝ) / (Fintype.card ι : ℝ)) * z^2 / z^2 := by
      exact (mul_div_cancel_right₀ _ (ne_of_gt hz2_pos)).symm
    _ ≤ 1 / z^2 := by
      exact div_le_div_of_nonneg_right h_div_card (le_of_lt hz2_pos)

end LeanSharp
