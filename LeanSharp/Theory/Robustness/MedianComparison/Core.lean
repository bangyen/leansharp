/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Robustness.FilteredMeanProps
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Linarith

/-!
# Median Robustness Core

This module exists to isolate the main boundedness and mean-comparison lemmas
used in robustness breakdown analyses.

## Theorems

* `mean_unbounded`: one-point contamination can drive empirical mean arbitrarily far.
* `median_bounded_subset`: geometric median remains bounded under strict fixed-point majority.
-/

namespace LeanSharp

variable {ι : Type*} [Fintype ι]
variable {α : Type*}

open BigOperators

/-- **Mean Non-Robustness**: A single large outlier can move the mean arbitrarily far. -/
lemma mean_unbounded [Nonempty ι] (s : Finset α) (g : α → W ι) (i0 : α)
    (hi0 : i0 ∈ s) (C : ℝ) :
    ∃ g' : α → W ι, (∀ i ≠ i0, g' i = g i) ∧ ‖empiricalMean s g'‖ > C := by
  classical
  let other_sum := ∑ i ∈ s.erase i0, g i
  let n := (s.card : ℝ)
  let v := (n * (|C| + 1) + ‖other_sum‖) • unitVector ι
  use fun i => if i = i0 then v else g i
  have h_norm_v : ‖v‖ = n * (|C| + 1) + ‖other_sum‖ := by
    rw [
      norm_smul,
      norm_unit_vector,
      mul_one,
      Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (mul_nonneg (by positivity) (by positivity)) (norm_nonneg _))
    ]
  constructor
  · intro i hi; simp only [if_neg hi]
  · unfold empiricalMean
    rw [
      ← Finset.insert_erase hi0,
      Finset.sum_insert (fun h => absurd rfl (Finset.mem_erase.mp h).left),
      Finset.sum_congr rfl (fun i hi => if_neg (Finset.mem_erase.1 hi).1),
      Finset.insert_erase hi0
    ]
    simp only [↓reduceIte]
    rw [show (s.erase i0).sum g = other_sum from rfl, show (s.card : ℝ) = n from rfl]
    have hn_pos : 0 < n := by have : s.Nonempty := ⟨i0, hi0⟩; positivity
    rw [norm_smul, Real.norm_eq_abs (1 / n), abs_of_pos (one_div_pos.mpr hn_pos)]
    have heq : (1 / n) * (‖v‖ - ‖other_sum‖) = (1 / n)
      * (n * (|C| + 1) + ‖other_sum‖ - ‖other_sum‖) := by rw [h_norm_v]
    have hring : (1 / n) * (n * (|C| + 1) + ‖other_sum‖ - ‖other_sum‖)
      = (1 / n) * (n * (|C| + 1)) := by ring
    have hlast : (1 / n) * (n * (|C| + 1)) = |C| + 1 :=
      by field_simp [hn_pos.ne.symm]
    have hineq : ‖v + other_sum‖ ≥ ‖v‖ - ‖other_sum‖ := by
      have H :=
        (norm_sub_norm_le v (-other_sum)).trans_eq (by rw [sub_neg_eq_add])
      have hneg : ‖v‖ - ‖-other_sum‖ = ‖v‖ - ‖other_sum‖ :=
        by rw [norm_neg other_sum]
      exact (ge_of_eq hneg).trans H
    have hchain := heq.trans (hring.trans hlast)
    have hge := ge_trans (mul_le_mul_of_nonneg_left hineq (one_div_pos.mpr hn_pos).le)
      (ge_of_eq hchain)
    have hC_lt_abs_add_one : C < |C| + 1 := by
      have hC_le_abs : C ≤ |C| := le_abs_self C
      linarith
    exact lt_of_lt_of_le hC_lt_abs_add_one hge

/-- **Median Robustness (Boundedness)**: The geometric median remains bounded even if
some points are moved, as long as a majority stay fixed.
This is a precursor to the 50% breakdown point. -/
theorem median_bounded_subset (s : Finset α) (g : α → W ι) (s_fixed : Finset α)
    (h_sub : s_fixed ⊆ s) (h_maj : 2 * s_fixed.card > s.card) :
    ∃ R_med : ℝ, ∀ g' : α → W ι, (∀ i ∈ s_fixed, g' i = g i) →
      ‖geometricMedian s g'‖ ≤ R_med := by
  classical
  have hs_nonempty : s.Nonempty := by
    by_contra h
    have heq : s = ∅ := (Finset.not_nonempty_iff_eq_empty (α := α)).1 h
    rw [heq, Finset.card_empty] at h_maj
    rw [heq] at h_sub
    rw [Finset.subset_empty.1 h_sub, Finset.card_empty, mul_zero] at h_maj
    exact Nat.not_lt_zero _ h_maj
  have h_fixed_nonempty : s_fixed.Nonempty := by
    by_contra h
    have heq : s_fixed = ∅ := (Finset.not_nonempty_iff_eq_empty (α := α)).1 h
    rw [heq, Finset.card_empty, mul_zero] at h_maj
    exact Nat.not_lt_zero _ h_maj
  let i0 := h_fixed_nonempty.choose
  have hi0 : i0 ∈ s_fixed := h_fixed_nonempty.choose_spec
  let C_fixed := 2 * ∑ i ∈ s_fixed, ‖g i - g i0‖
  let n := (s.card : ℝ)
  let nf := (s_fixed.card : ℝ)
  let K := 2 * nf - n
  have hK_pos : 0 < K := by
    have H : (2 : ℝ) * (s_fixed.card : ℝ) > (s.card : ℝ) := mod_cast h_maj
    exact sub_pos.mpr H
  use ‖g i0‖ + C_fixed / K
  intro g' hg'
  let m := geometricMedian s g'
  have h_min : (fun x => ∑ i ∈ s, ‖g' i - x‖) m ≤ (∑ i ∈ s, ‖g' i - g i0‖) := by
    rw [show m = geometricMedian s g' from rfl]
    have H : ∀ x ∈ Set.univ, (fun m => ∑ i ∈ s, ‖g' i - m‖)
        (geometricMedian s g') ≤ (fun m => ∑ i ∈ s, ‖g' i - m‖) x := by
      unfold geometricMedian; rw [dif_pos hs_nonempty]
      exact Classical.choose_spec (exists_isMin_on_finite_sum_norm s g')
    exact H (g i0) (Set.mem_univ (g i0))
  let s_out := s \ s_fixed
  have h_split (x : W ι) : ∑ i ∈ s, ‖g' i - x‖
      = (∑ i ∈ s_fixed, ‖g i - x‖) + (∑ i ∈ s_out, ‖g' i - x‖) := by
    rw [← Finset.sdiff_union_of_subset h_sub]
    rw [Finset.sum_union (Finset.disjoint_iff_inter_eq_empty.2 (Finset.sdiff_inter_self s_fixed s))]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl (fun i hi => congr_arg (fun w => ‖w - x‖) (hg' i hi))
  rw [show (fun x => ∑ i ∈ s, ‖g' i - x‖) m = ∑ i ∈ s, ‖g' i - m‖ from rfl] at h_min
  rw [h_split m, h_split (g i0)] at h_min
  have h_dist_bound : K * ‖m - g i0‖ ≤ C_fixed := by
    have h1 : ∑ i ∈ s_fixed, ‖g i - m‖ ≥
        nf * ‖m - g i0‖ - (∑ i ∈ s_fixed, ‖g i - g i0‖) := by
      calc (∑ i ∈ s_fixed, ‖g i - m‖) ≥
          ∑ i ∈ s_fixed, (‖m - g i0‖ - ‖g i - g i0‖) :=
            Finset.sum_le_sum (fun i _ => by
              have H := norm_sub_norm_le (m - g i0) (g i - g i0)
              rw [show (m - g i0) - (g i - g i0) = m - g i from by abel] at H
              rw [norm_sub_rev m (g i)] at H
              exact H)
        _ = nf * ‖m - g i0‖ - ∑ i ∈ s_fixed, ‖g i - g i0‖ := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have h2 : (∑ i ∈ s_out, ‖g' i - g i0‖) - (∑ i ∈ s_out, ‖g' i - m‖)
        ≤ (s_out.card : ℝ) * ‖m - g i0‖ := by
      calc (∑ i ∈ s_out, ‖g' i - g i0‖) - (∑ i ∈ s_out, ‖g' i - m‖)
          = ∑ i ∈ s_out, (‖g' i - g i0‖ - ‖g' i - m‖) := by rw [Finset.sum_sub_distrib]
        _ ≤ ∑ i ∈ s_out, ‖m - g i0‖ := by
          apply Finset.sum_le_sum; intro i _
          have H := norm_sub_norm_le (g' i - g i0) (g' i - m)
          rw [show (g' i - g i0) - (g' i - m) = m - g i0 from by abel] at H; exact H
        _ = (s_out.card : ℝ) * ‖m - g i0‖ := by rw [Finset.sum_const, nsmul_eq_mul]
    have h_out_card : (s_out.card : ℝ) = n - nf := by
      rw [Finset.card_sdiff, Finset.inter_comm, Finset.inter_eq_right.2 h_sub,
          Nat.cast_sub (Finset.card_le_card h_sub)]
    rw [h_out_card] at h2
    linarith
  calc ‖geometricMedian s g'‖ = ‖m‖ := by rw [show m = geometricMedian s g' from rfl]
    _ ≤ ‖m - g i0‖ + ‖g i0‖ := by rw [add_comm]; apply norm_le_insert'
    _ ≤ C_fixed / K + ‖g i0‖ := by
      have hdiv : ‖m - g i0‖ ≤ C_fixed / K := by
        have H := mul_le_mul (α := ℝ) (le_refl K⁻¹) h_dist_bound
          (mul_nonneg (le_of_lt hK_pos) (norm_nonneg _)) (inv_pos.mpr hK_pos).le
        have H2 : K⁻¹ * K = (1 : ℝ) := by field_simp [ne_of_gt hK_pos]
        rw [← mul_assoc, H2, one_mul, mul_comm] at H
        rwa [div_eq_inv_mul C_fixed K, mul_comm]
      rw [add_comm (‖m - g i0‖), add_comm (C_fixed / K)]
      exact add_le_add_right hdiv ‖g i0‖
    _ = ‖g i0‖ + C_fixed / K := add_comm _ _

end LeanSharp
