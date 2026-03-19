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
# Filtered Mean Robustness

This module exists to isolate filtered empirical-mean definitions and bounds so
other robustness proofs can depend on a compact, reusable mean-aggregation API.

## Definitions

* `unitVector`.
* `empiricalMean`.
* `zFilteredEmpiricalMean`.
* `RobustSample`: Bundles a sample set `s`, a mapping `g`, and fixed-subset/radius
  bounds for robustness analysis.

## Theorems

* `norm_unit_vector`.
* `z_filtered_empirical_mean_norm_le`.
* `z_filtered_empirical_mean_norm_le_of_pointwise_bound`.
* `z_filtered_empirical_mean_bounded_subset`.
* `z_filtered_empirical_mean_bounded_subset_max`.
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

/-- **Subset-robust filtered-mean bound**: if indices in `s_fixed` are unchanged and bounded
by `R_fixed`, while changed indices in `s \ s_fixed` are bounded by `R_out`, then the
Z-filtered empirical mean is bounded by the corresponding weighted average radius. -/
theorem z_filtered_empirical_mean_bounded_subset [DecidableEq α]
    (S : RobustSample α ι) (z : ℝ) (hs : S.s.Nonempty) :
    ∀ g' : α → W ι, (∀ i ∈ S.s_fixed, g' i = S.g i) →
      (∀ i ∈ S.s \ S.s_fixed, ‖g' i‖ ≤ S.R_out) →
      ‖zFilteredEmpiricalMean S.s g' z‖ ≤
        (1 / (S.s.card : ℝ)) *
          (((S.s_fixed.card : ℝ) * S.R_fixed) + (((S.s \ S.s_fixed).card : ℝ) * S.R_out)) := by
  intro g' hg_fixed hg_out
  let s_out := S.s \ S.s_fixed
  have h_base := z_filtered_empirical_mean_norm_le S.s g' z hs
  have h_sum_split_raw :
      ∑ i ∈ S.s, ‖g' i‖ =
        (∑ i ∈ S.s_fixed, ‖g' i‖) + (∑ i ∈ S.s \ S.s_fixed, ‖g' i‖) := by
    have h_filter_eq : S.s.filter (fun i => i ∈ S.s_fixed) = S.s_fixed := by
      ext i
      constructor
      · intro hi
        exact (Finset.mem_filter.mp hi).2
      · intro hi
        exact Finset.mem_filter.mpr ⟨S.h_sub hi, hi⟩
    have h_filter_not_eq : S.s.filter (fun i => i ∉ S.s_fixed) = S.s \ S.s_fixed := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_sdiff]
    simpa only [Finset.sum_filter, h_filter_eq, h_filter_not_eq] using
      (Finset.sum_filter_add_sum_filter_not
        (s := S.s) (f := fun i => ‖g' i‖) (p := fun i => i ∈ S.s_fixed)).symm
  have h_sum_split :
      ∑ i ∈ S.s, ‖g' i‖ =
      (∑ i ∈ S.s_fixed, ‖g' i‖) + (∑ i ∈ s_out, ‖g' i‖) := by
    simpa only [s_out] using h_sum_split_raw
  have h_fixed_sum : (∑ i ∈ S.s_fixed, ‖g' i‖) ≤
      ∑ i ∈ S.s_fixed, S.R_fixed := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    calc ‖g' i‖ = ‖S.g i‖ := by rw [hg_fixed i hi]
      _ ≤ S.R_fixed := S.h_fixed_bound i hi
  have h_out_sum : (∑ i ∈ s_out, ‖g' i‖) ≤ ∑ i ∈ s_out, S.R_out := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    exact hg_out i (by simpa only [s_out] using hi)
  have h_sum_bound : (1 / (S.s.card : ℝ)) * (∑ i ∈ S.s, ‖g' i‖)
      ≤ (1 / (S.s.card : ℝ)) *
        ((∑ i ∈ S.s_fixed, S.R_fixed) + (∑ i ∈ s_out, S.R_out)) := by
    apply mul_le_mul_of_nonneg_left
    · rw [h_sum_split]
      exact add_le_add h_fixed_sum h_out_sum
    · positivity
  have h_sum_bound' : (1 / (S.s.card : ℝ)) * (∑ i ∈ S.s, ‖g' i‖)
      ≤ (1 / (S.s.card : ℝ)) *
          (((S.s_fixed.card : ℝ) * S.R_fixed) + (((S.s \ S.s_fixed).card : ℝ) * S.R_out)) := by
    calc
      (1 / (S.s.card : ℝ)) * (∑ i ∈ S.s, ‖g' i‖)
        ≤ (1 / (S.s.card : ℝ)) *
          ((∑ i ∈ S.s_fixed, S.R_fixed) + (∑ i ∈ s_out, S.R_out)) := h_sum_bound
      _ = (1 / (S.s.card : ℝ)) *
          (((S.s_fixed.card : ℝ) * S.R_fixed) + ((s_out.card : ℝ) * S.R_out)) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.sum_const, nsmul_eq_mul]
      _ = (1 / (S.s.card : ℝ)) *
            (((S.s_fixed.card : ℝ) * S.R_fixed) +
              (((S.s \ S.s_fixed).card : ℝ) * S.R_out)) := by
            simp only [one_div, s_out]
  exact h_base.trans h_sum_bound'

/-- **Max-radius subset bound**: under the same fixed/outlier split assumptions as
`z_filtered_empirical_mean_bounded_subset`, the filtered mean is bounded by the larger
radius `max R_fixed R_out`. This provides a simple estimator-safety certificate. -/
theorem z_filtered_empirical_mean_bounded_subset_max [DecidableEq α]
    (S : RobustSample α ι) (z : ℝ) (hs : S.s.Nonempty) :
    ∀ g' : α → W ι, (∀ i ∈ S.s_fixed, g' i = S.g i) →
      (∀ i ∈ S.s \ S.s_fixed, ‖g' i‖ ≤ S.R_out) →
      ‖zFilteredEmpiricalMean S.s g' z‖ ≤ max S.R_fixed S.R_out :=
    by
  intro g' hg_fixed hg_out
  have h_weighted := z_filtered_empirical_mean_bounded_subset S z hs g' hg_fixed hg_out
  have hn_pos : 0 < (S.s.card : ℝ) := by exact_mod_cast hs.card_pos
  have h_card :
      ((S.s \ S.s_fixed).card : ℝ) = (S.s.card : ℝ) - (S.s_fixed.card : ℝ) := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.2 S.h_sub]
    exact Nat.cast_sub (Finset.card_le_card S.h_sub)
  have h_num_le :
      ((S.s_fixed.card : ℝ) * S.R_fixed) + (((S.s \ S.s_fixed).card : ℝ) * S.R_out)
        ≤ ((S.s.card : ℝ) * (max S.R_fixed S.R_out)) := by
    have h_fix_le :
        (S.s_fixed.card : ℝ) * S.R_fixed ≤ (S.s_fixed.card : ℝ) *
          (max S.R_fixed S.R_out) := by
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
    have h_out_le :
        ((S.s \ S.s_fixed).card : ℝ) * S.R_out
          ≤ ((S.s \ S.s_fixed).card : ℝ) * (max S.R_fixed S.R_out) := by
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
    have h_add := add_le_add h_fix_le h_out_le
    rw [h_card] at h_add ⊢
    have h_expand :
        (S.s_fixed.card : ℝ) * max S.R_fixed S.R_out +
            ((S.s.card : ℝ) - (S.s_fixed.card : ℝ)) * max S.R_fixed S.R_out
          = (S.s.card : ℝ) * max S.R_fixed S.R_out := by ring
    exact h_add.trans_eq h_expand
  have h_div :
      (1 / (S.s.card : ℝ)) *
          ((((S.s_fixed.card : ℝ) * S.R_fixed) + (((S.s \ S.s_fixed).card : ℝ) * S.R_out)))
        ≤ max S.R_fixed S.R_out := by
    calc
      (1 / (S.s.card : ℝ)) *
          ((((S.s_fixed.card : ℝ) * S.R_fixed) + (((S.s \ S.s_fixed).card : ℝ) * S.R_out)))
        ≤ (1 / (S.s.card : ℝ)) * ((S.s.card : ℝ) * (max S.R_fixed S.R_out)) := by
          exact mul_le_mul_of_nonneg_left h_num_le (by positivity)
      _ = max S.R_fixed S.R_out := by
          field_simp [ne_of_gt hn_pos]
  exact h_weighted.trans h_div

end LeanSharp
