/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Theory.Robustness.ComparisonResults

/-!
# Robustness Interface Tests

This module verifies that robustness-comparison interface theorems compose
cleanly in downstream theorem statements.

## Theorems

* `bounded_outlier_robustness_interface_test`.
* `unbounded_outlier_preference_interface_test`.
-/

namespace LeanSharp

/-- **Bounded-Outlier Robustness Verification**: checks that majority-fixed and
bounded-outlier assumptions are sufficient to obtain simultaneous geometric-median
and Z-filtered-mean boundedness guarantees. -/
theorem bounded_outlier_robustness_interface_test
    {ι α : Type*}
    [Fintype ι]
    [DecidableEq α]
    (s : Finset α) (g : α → W ι)
    (s_fixed : Finset α) (h_sub : s_fixed ⊆ s) (h_maj : 2 * s_fixed.card > s.card)
    (z R_fixed R_out : ℝ) (hs : s.Nonempty)
    (h_fixed_bound : ∀ i ∈ s_fixed, ‖g i‖ ≤ R_fixed) :
    ∃ R_med : ℝ, ∀ g' : α → W ι, (∀ i ∈ s_fixed, g' i = g i) →
      (∀ i ∈ s \ s_fixed, ‖g' i‖ ≤ R_out) →
      ‖geometric_median s g'‖ ≤ R_med
        ∧ ‖z_filtered_empirical_mean s g' z‖ ≤ max R_fixed R_out := by
  exact median_and_zfiltered_mean_bounded_subset
    s g s_fixed h_sub h_maj z R_fixed R_out hs h_fixed_bound

/-- **Unbounded-Outlier Preference Verification**: checks that the comparison
theorem exposes the regime where median aggregation is robust while mean is not. -/
theorem unbounded_outlier_preference_interface_test
    {ι α : Type*}
    [Fintype ι]
    [Nonempty ι]
    (s : Finset α) (g : α → W ι)
    (i0 : α) (hi0 : i0 ∈ s) (h_card : 3 ≤ s.card) (C : ℝ) (hC : -1 ≤ C) :
    (∃ R : ℝ, ∀ g' : α → W ι, (∀ i ≠ i0, g' i = g i) →
        ‖geometric_median s g'‖ ≤ R) ∧
      (∃ g' : α → W ι, (∀ i ≠ i0, g' i = g i) ∧ ‖empirical_mean s g'‖ > C) := by
  exact prefer_median_for_unbounded_one_outlier s g i0 hi0 h_card C hC

end LeanSharp
