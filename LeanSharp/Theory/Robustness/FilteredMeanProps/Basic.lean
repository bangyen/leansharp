/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Core.Stats
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Filtered Mean Robustness - Basic Definitions

This module provides definitions for empirical means and coordinate-wise Z-score
filtering, along with basic norm control lemmas.

## Main Definitions
* `empiricalMean`: Standard average of vector-valued samples.
* `zFilteredEmpiricalMean`: Mean computed after coordinate-wise Z-score gating.

## Main Theorems
* `z_filtered_empirical_mean_norm_le`: Quantitative handle for robust bounds.
-/

namespace LeanSharp

variable {ι : Type*} [Fintype ι]
variable {α : Type*}

/-- A structure bundling a sample model with fixed and outlier radius bounds. -/
structure RobustSample (α ι : Type*) [Fintype ι] [DecidableEq α] where
  /-- The set of data point indices. -/
  s : Finset α
  /-- The mapping from indices to weight vectors. -/
  g : α → W ι
  /-- The subset of fixed (uncorrupted) data points. -/
  s_fixed : Finset α
  /-- Proof that the fixed subset is indeed part of the sample. -/
  h_sub : s_fixed ⊆ s
  /-- Radius bound for uncorrupted points. -/
  R_fixed : ℝ
  /-- Radius bound for outliers. -/
  R_out : ℝ
  /-- Proof that uncorrupted points satisfy the radius bound. -/
  h_fixed_bound : ∀ i ∈ s_fixed, ‖g i‖ ≤ R_fixed

open BigOperators

/-- A constant unit vector in $W$. -/
noncomputable def unitVector (ι : Type*) [Fintype ι] : W ι :=
  WithLp.equiv 2 (ι → ℝ) |>.symm fun _ => 1 / Real.sqrt (Fintype.card ι)

lemma norm_unit_vector (ι : Type*) [Fintype ι] [Nonempty ι] : ‖unitVector ι‖ = 1 := by
  unfold unitVector
  rw [EuclideanSpace.norm_eq]
  simp only [WithLp.equiv_symm_apply, Real.norm_eq_abs, sq_abs]
  have card_pos : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_sq : (1 / Real.sqrt (Fintype.card ι))^2 = 1 / (Fintype.card ι : ℝ) := by
    rw [one_div, inv_pow, Real.sq_sqrt card_pos]; field_simp
  simp only [h_sq]
  have card_ne_zero : (Fintype.card ι : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := ι))
  rw [mul_one_div_cancel card_ne_zero, Real.sqrt_one]

/-- The empirical mean of a collection of vectors. -/
noncomputable def empiricalMean (s : Finset α) (g : α → W ι) : W ι :=
  (1 / (s.card : ℝ)) • ∑ i ∈ s, g i

/-- The empirical mean after applying coordinate-wise Z-score filtering to each vector.
This estimator starts the bridge between classical outlier robustness and Z-score gating. -/
noncomputable def zFilteredEmpiricalMean (s : Finset α) (g : α → W ι) (z : ℝ) : W ι :=
  empiricalMean s (fun i => filteredGradient (g i) z)

/-- **Filtered mean norm control**: the norm of the Z-filtered empirical mean is bounded
by the average unfiltered norm over the sample. This gives a direct quantitative handle
for robust bounds that combine filtering with aggregation. -/
theorem z_filtered_empirical_mean_norm_le
    (s : Finset α) (g : α → W ι) (z : ℝ) (hs : s.Nonempty) :
    ‖zFilteredEmpiricalMean s g z‖ ≤ (1 / (s.card : ℝ)) * (∑ i ∈ s, ‖g i‖) := by
  unfold zFilteredEmpiricalMean empiricalMean
  have hn_pos : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hn_pos)]
  calc
    (1 / (s.card : ℝ)) * ‖∑ i ∈ s, filteredGradient (g i) z‖
      ≤ (1 / (s.card : ℝ)) * (∑ i ∈ s, ‖filteredGradient (g i) z‖) := by
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (1 / (s.card : ℝ)) * (∑ i ∈ s, ‖g i‖) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum (fun i _ => norm_filteredGradient_le (g i) z)
        · positivity

/-- **Uniform-input bound for filtered mean**: if every sample gradient has norm at most
`R`, then the Z-filtered empirical mean also has norm at most `R`. This is the first
reusable step toward deciding when filtered-mean aggregation is safe. -/
theorem z_filtered_empirical_mean_norm_le_of_pointwise_bound
    (s : Finset α) (g : α → W ι) (z R : ℝ) (hs : s.Nonempty)
    (hR : ∀ i ∈ s, ‖g i‖ ≤ R) :
    ‖zFilteredEmpiricalMean s g z‖ ≤ R := by
  have h_base := z_filtered_empirical_mean_norm_le s g z hs
  have hn_pos : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  refine h_base.trans ?_
  calc
    (1 / (s.card : ℝ)) * (∑ i ∈ s, ‖g i‖)
      ≤ (1 / (s.card : ℝ)) * (∑ i ∈ s, R) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum (fun i hi => hR i hi)
        · positivity
    _ = (1 / (s.card : ℝ)) * ((s.card : ℝ) * R) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = R := by
        field_simp [ne_of_gt hn_pos]

end LeanSharp
