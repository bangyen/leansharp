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
* `zScoreMask_coverage`: the fraction of components kept by the mask (within `zσ` of the
  mean) is at least `1 - 1/z²`.
-/
namespace LeanSharp
open Finset BigOperators Real
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The subset of indices in the Z-score tail, i.e. components at least `zσ` from the mean.
    These are the components *discarded* by the corrected `zScoreMask`; its kept set is the
    complementary within-threshold set. -/
noncomputable def zScoreTails (g : W ι) (z : ℝ) : Finset ι :=
  univ.filter fun i => |(WithLp.equiv 2 (ι → ℝ) g) i - vectorMean g| ≥ z * vectorStd g

/-- **Discrete Chebyshev's Inequality for Vectors**:
For any $z > 0$, the fraction of coordinates falling in the $z$-standard
deviation tail is bounded by $1/z^2$ when variance is non-zero.
This bounds the fraction of components the corrected mask discards. -/
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

/-- **Z-Score Mask Coverage**: the fraction of components kept by the corrected mask —
those within `zσ` of the mean — is at least `1 - 1/z²`. The filter keeps most
components and discards at most a `1/z²` tail fraction. -/
theorem zScoreMask_coverage (g : W ι) {z : ℝ} (hz : 0 < z) (hvar : vectorVariance g > 0) :
    (1 - 1 / z^2) ≤
      ((univ.filter fun i =>
        |(WithLp.equiv 2 (ι → ℝ) g) i - vectorMean g| ≤ z * vectorStd g).card : ℝ)
        / (Fintype.card ι : ℝ) := by
  classical
  let I : Finset ι := univ.filter fun i =>
    |(WithLp.equiv 2 (ι → ℝ) g) i - vectorMean g| ≤ z * vectorStd g
  let T : Finset ι := zScoreTails g z
  have h_cheb := chebyshev_vector g hz hvar
  have h_sub : (univ \ T) ⊆ I := by
    intro i hi
    have hi_not : i ∉ T := (Finset.mem_sdiff.mp hi).2
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
    have h_ge : ¬ z * vectorStd g ≤ |(WithLp.equiv 2 (ι → ℝ) g) i - vectorMean g| := by
      intro hg
      have h_in_T : i ∈ T := by
        simp only [T, zScoreTails, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hg
      exact hi_not h_in_T
    exact le_of_lt (lt_of_not_ge h_ge)
  have h_card_le : (Fintype.card ι : ℝ) - (T.card : ℝ) ≤ (I.card : ℝ) := by
    have hsub : (univ \ T).card ≤ I.card := Finset.card_le_card h_sub
    have hT_le : T.card ≤ Fintype.card ι := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ T)
    have hsd : (univ \ T).card = (Fintype.card ι : ℕ) - T.card := by
      rw [← Finset.card_univ]
      rw [Finset.card_sdiff]
      simp only [Finset.inter_univ]
    have hsub_nat : (Fintype.card ι : ℕ) - T.card ≤ I.card := by
      rwa [← hsd]
    exact_mod_cast hsub_nat
  have h_card_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by positivity
  have h_frac : 1 - (T.card : ℝ) / (Fintype.card ι : ℝ) ≤
      (I.card : ℝ) / (Fintype.card ι : ℝ) := by
    have h_div := div_le_div_of_nonneg_right h_card_le (le_of_lt h_card_pos)
    rw [sub_div] at h_div
    rw [div_self (ne_of_gt h_card_pos)] at h_div
    exact h_div
  have h_tail : (T.card : ℝ) / (Fintype.card ι : ℝ) ≤ 1 / z^2 := h_cheb
  linarith

end LeanSharp
