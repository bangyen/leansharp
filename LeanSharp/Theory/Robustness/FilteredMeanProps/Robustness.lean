/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Robustness.FilteredMeanProps.Basic

/-!
# Filtered Mean Robustness - Robust Bounds

This module establishes quantitative robustness bounds for filtered empirical means
under fixed-subset and outlier radius assumptions.

## Main Theorems
* `z_filtered_empirical_mean_bounded_subset`: Weighted average radius bound.
* `z_filtered_empirical_mean_bounded_subset_max`: Simple safety certificate.
-/

namespace LeanSharp

variable {ι : Type*} [Fintype ι]
variable {α : Type*}

open BigOperators

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
