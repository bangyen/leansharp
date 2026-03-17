/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Robustness.MedianComparison

/-!
# Robustness Comparison Results

This module exists to collect high-level comparison theorems that combine core
median and mean robustness lemmas into user-facing statements.

## Theorems

* `median_bounded_mean_unbounded_one_outlier`.
* `median_robust_mean_nonrobust`.
-/

namespace LeanSharp

variable {ι : Type*} [Fintype ι]
variable {α : Type*}

/-- **Median vs mean under one outlier**: With a single movable point, the empirical mean
can be made arbitrarily large while the geometric median stays bounded (when the sample has
at least three points). So median-based aggregation is robust and mean-based is not. -/
theorem median_bounded_mean_unbounded_one_outlier [Nonempty ι] (s : Finset α) (g : α → W ι)
    (i0 : α) (hi0 : i0 ∈ s) (h_card : 3 ≤ s.card) (C : ℝ) (hC : -1 ≤ C) :
    (∃ R : ℝ, ∀ g' : α → W ι, (∀ i ≠ i0, g' i = g i) →
        ‖geometric_median s g'‖ ≤ R) ∧
    (∃ g' : α → W ι, (∀ i ≠ i0, g' i = g i) ∧ ‖empirical_mean s g'‖ > C) := by
  classical
  have h_maj : 2 * (s.erase i0).card > s.card := by
    rw [Finset.card_erase_of_mem hi0]; omega
  constructor
  · obtain ⟨R, hR⟩ := median_bounded_subset s g (s.erase i0) (Finset.erase_subset i0 s) h_maj
    refine ⟨R, fun g' hg' => hR g' (fun i hi => hg' i (Finset.mem_erase.1 hi).1)⟩
  · exact mean_unbounded s g i0 hi0 C hC

/-- **Generalized Robustness Comparison**:
In the presence of $K$ arbitrary outliers (where $2K < n$), the empirical mean can be made
arbitrarily large while the geometric median remains bounded. This formally proves that
median-based aggregation is inherently robust to multiple malicious outliers while the
mean is not. -/
theorem median_robust_mean_nonrobust [Nonempty ι] [DecidableEq α] (s : Finset α) (g : α → W ι)
    (s_fixed : Finset α) (h_sub : s_fixed ⊆ s) (h_maj : 2 * s_fixed.card > s.card)
    (C : ℝ) (hC : -1 ≤ C) :
    (∃ R : ℝ, ∀ g' : α → W ι, (∀ i ∈ s_fixed, g' i = g i) →
        ‖geometric_median s g'‖ ≤ R) ∧
    (∀ i0 ∈ s \ s_fixed, ∃ g' : α → W ι, (∀ i ≠ i0, g' i = g i) ∧ ‖empirical_mean s g'‖ > C) := by
  constructor
  · exact median_bounded_subset s g s_fixed h_sub h_maj
  · intro i0 hi0
    have hi0_s : i0 ∈ s := (Finset.mem_sdiff.1 hi0).1
    exact mean_unbounded s g i0 hi0_s C hC

end LeanSharp
