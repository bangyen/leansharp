/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Robustness.MedianComparison.Core

/-!
# Median Breakdown Point

This module exists to isolate the unbounded side of the 50% breakdown-point
characterization for the geometric median.

## Theorems

* `median_breakdown`: strict minority of fixed points implies unbounded contamination effect.
-/

namespace LeanSharp

variable {ι : Type*} [Fintype ι]
variable {α : Type*}

open BigOperators

/-- **50% breakdown point (unbounded side)**: When strictly fewer than half the points
are fixed, an adversary can move the remaining points so that the geometric median
has arbitrarily large norm. Together with `median_bounded_subset` this characterizes
the 50% breakdown point: the median stays bounded iff more than half the points are fixed. -/
theorem median_breakdown [Nonempty ι] (s : Finset α) (g : α → W ι) (s_fixed : Finset α)
    (h_sub : s_fixed ⊆ s) (h_break : 2 * s_fixed.card < s.card) (C : ℝ) :
    ∃ g' : α → W ι, (∀ i ∈ s_fixed, g' i = g i) ∧ ‖geometricMedian s g'‖ > C := by
  classical
  have hs_nonempty : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.card_empty] at h_break
    exact Nat.not_lt_zero _ h_break
  let s_out := s \ s_fixed
  have h_out_card : s_out.card = s.card - s_fixed.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.2 h_sub]
  have h_nout_gt_nfixed : (s_fixed.card : ℝ) < (s_out.card : ℝ) := by
    rw [h_out_card, Nat.cast_sub (Finset.card_le_card h_sub)]
    have H : (2 : ℝ) * (s_fixed.card : ℝ) < (s.card : ℝ) := mod_cast h_break
    linarith
  have h_denom_pos : 0 < (s_out.card : ℝ) - (s_fixed.card : ℝ) := sub_pos.mpr h_nout_gt_nfixed
  set B := ∑ i ∈ s_fixed, ‖g i‖
  set n_out := (s_out.card : ℝ)
  set n_fixed := (s_fixed.card : ℝ)
  set R := max (|C| + 2) ((n_out * C + B) / (n_out - n_fixed) + 1)
  have hR_ge : R ≥ 0 := by unfold R; apply le_max_iff.mpr; left; positivity
  have hR_gt_C : C < R := by
    unfold R
    have hC_lt_abs_add_two : C < |C| + 2 := by
      have hC_le_abs : C ≤ |C| := le_abs_self C
      linarith
    exact lt_of_lt_of_le hC_lt_abs_add_two (le_max_left _ _)
  have hR_large : (n_out * C + B) / (n_out - n_fixed) < R := by
    unfold R
    have h1 := le_max_right (|C| + 2) ((n_out * C + B) / (n_out - n_fixed) + 1)
    linarith
  use fun i => if i ∈ s_out then R • unitVector ι else g i
  constructor
  · intro i hi
    split_ifs with h
    · exact absurd hi (Finset.mem_sdiff.1 h).2
    · rfl
  · set g' := fun i => if i ∈ s_out then R • unitVector ι else g i
    set m := geometricMedian s g'
    have hg'_fixed : ∀ i ∈ s_fixed, g' i = g i := by
      intro i hi; simp only [g']; split_ifs with h
      · exact absurd hi (Finset.mem_sdiff.1 h).2
      · rfl
    have hg'_out : ∀ i ∈ s_out, g' i = R • unitVector ι := by
      intro i hi; simp only [g']; rw [if_pos hi]
    have hm_min : ∀ x : W ι, ∑ i ∈ s, ‖g' i - m‖ ≤ ∑ i ∈ s, ‖g' i - x‖ := by
      intro x
      have h_m_choice : m = Classical.choose (exists_isMin_on_finite_sum_norm s g') :=
        geometricMedian_eq_choose s g' hs_nonempty
      rw [h_m_choice]
      exact Classical.choose_spec
        (exists_isMin_on_finite_sum_norm s g') (Set.mem_univ x)
    by_contra h_norm_le
    push_neg at h_norm_le
    set v := R • unitVector ι
    have h_sum_at_m : ∑ i ∈ s, ‖g' i - m‖ =
        (∑ i ∈ s_fixed, ‖g i - m‖) + ∑ i ∈ s_out, ‖v - m‖ := by
      rw [← Finset.sdiff_union_of_subset h_sub,
        Finset.sum_union (Finset.disjoint_iff_inter_eq_empty.2 (Finset.sdiff_inter_self s_fixed s)),
        add_comm]
      congr 1
      · refine Finset.sum_congr rfl (fun i hi => congr_arg (‖· - m‖) (hg'_fixed i hi))
      · refine Finset.sum_congr rfl (fun i hi => congr_arg (‖· - m‖) (hg'_out i hi))
    have h_norm_v : ‖v‖ = R := by
      rw [norm_smul, norm_unit_vector, mul_one, Real.norm_eq_abs, abs_of_nonneg hR_ge]
    have h_lower : ∑ i ∈ s_fixed, ‖g i - m‖ + ∑ i ∈ s_out, ‖v - m‖ ≥
        (n_out : ℝ) * (R - C) := by
      have h1 : ∑ i ∈ s_out, ‖v - m‖ ≥ (n_out : ℝ) * (R - C) := by
        have h1' : ∑ i ∈ s_out, ‖v - m‖ ≥ ∑ i ∈ s_out, (R - C) := by
          apply Finset.sum_le_sum; intro i _
          have H := norm_sub_norm_le v m
          rw [h_norm_v] at H
          have hR_C : R - C ≤ R - ‖m‖ := sub_le_sub_left h_norm_le R
          exact hR_C.trans H
        rw [Finset.sum_const, nsmul_eq_mul, Finset.sum_const, nsmul_eq_mul] at h1'
        rw [Finset.sum_const, nsmul_eq_mul,
          show (s_out.card : ℝ) = n_out from rfl]
        exact h1'
      have h2 : 0 ≤ ∑ i ∈ s_fixed, ‖g i - m‖ :=
        Finset.sum_nonneg (fun _ _ => norm_nonneg _)
      exact (zero_add (n_out * (R - C))).symm.le.trans (add_le_add h2 h1)
    have h_upper : ∑ i ∈ s, ‖g' i - v‖ ≤ B + n_fixed * R := by
      rw [← Finset.sdiff_union_of_subset h_sub,
        Finset.sum_union (Finset.disjoint_iff_inter_eq_empty.2 (Finset.sdiff_inter_self s_fixed s))]
      have h_fixed : ∑ i ∈ s_fixed, ‖g' i - v‖ = ∑ i ∈ s_fixed, ‖g i - v‖ := by
        refine Finset.sum_congr rfl (fun i hi => congr_arg (‖· - v‖) (hg'_fixed i hi))
      rw [h_fixed]
      have h_out : ∑ i ∈ s_out, ‖g' i - v‖ = 0 := by
        rw [Finset.sum_eq_zero]; intro i hi; rw [hg'_out i hi, sub_self, norm_zero]
      rw [h_out, zero_add]
      trans ∑ i ∈ s_fixed, (‖g i‖ + ‖v‖)
      · exact Finset.sum_le_sum (fun i _ => norm_sub_le (g i) v)
      · rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, h_norm_v]
    have h_eq : ∑ i ∈ s, ‖g' i - m‖ =
        (∑ i ∈ s_fixed, ‖g i - m‖) + ∑ i ∈ s_out, ‖v - m‖ :=
      h_sum_at_m
    have h_m_le_v := hm_min v
    have h_sum_at_v : ∑ i ∈ s, ‖g' i - v‖ = ∑ i ∈ s_fixed, ‖g i - v‖ + 0 := by
      rw [← Finset.sdiff_union_of_subset h_sub,
        Finset.sum_union (Finset.disjoint_iff_inter_eq_empty.2 (Finset.sdiff_inter_self s_fixed s)),
        add_comm]
      congr 1
      · refine Finset.sum_congr rfl (fun i hi => congr_arg (‖· - v‖) (hg'_fixed i hi))
      · rw [Finset.sum_eq_zero]; intro i hi; rw [hg'_out i hi, sub_self, norm_zero]
    rw [h_eq] at hm_min
    rw [h_sum_at_v] at h_m_le_v
    have h_v_ub : ∑ i ∈ s_fixed, ‖g i - v‖ ≤ B + n_fixed * R := by
      trans ∑ i ∈ s_fixed, (‖g i‖ + ‖v‖)
      · exact Finset.sum_le_sum (fun i _ => norm_sub_le (g i) v)
      · rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, h_norm_v]
    have key : R * (n_out - n_fixed) ≤ n_out * C + B := by
      rw [h_eq, add_zero] at h_m_le_v
      have := h_lower.trans (h_m_le_v.trans h_v_ub)
      nlinarith
    have hR_large' : (n_out * C + B) < R * (n_out - n_fixed) := by
      have := mul_lt_mul_of_pos_right hR_large h_denom_pos
      have H : (n_out * C + B) / (n_out - n_fixed) * (n_out - n_fixed) = n_out * C + B := by
        field_simp [ne_of_gt h_denom_pos]
      rwa [H] at this
    nlinarith [key, hR_large']

end LeanSharp
