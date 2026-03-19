/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Landscape
import LeanSharp.Theory.Robustness.BreakdownPoint
import LeanSharp.Theory.Robustness.ComparisonResults

/-!
# Robustness Tests

This module verifies the breakdown point theorems for the empirical mean
and the geometric median, as well as high-level comparison results.

## Examples
-/

namespace LeanSharp.Tests

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Test witness: for a non-empty dataset, the mean breakdown point is bounded by 1/n. -/
example [Nonempty ι] (s : Finset ℕ) (g : ℕ → W ι) (hs : s.Nonempty) :
    finiteSampleBreakdownPoint s g (empiricalMean s) ≤ 1 / (s.card : ℝ) :=
  mean_breakdown_point_zero s g hs

/-- Test witness: for any dataset, the geometric median has a breakdown point of at least 1/2. -/
example (s : Finset ℕ) (g : ℕ → W ι) (hs : s.Nonempty) :
    finiteSampleBreakdownPoint s g (geometricMedian s) ≥ 1 / 2 :=
  geometric_median_breakdown_point_ge_half s g hs

/-- Test witness (majority separation): for a single movable point and a strict
majority of fixed points, the empirical mean can be made arbitrarily large
while the geometric median stays bounded. -/
example [Nonempty ι] (s : Finset ℕ) (g : ℕ → W ι) (i0 : ℕ) (hi0 : i0 ∈ s)
    (h_maj : 2 * (s.erase i0).card > s.card) (C : ℝ) :
    (∃ R : ℝ, ∀ g' : ℕ → W ι, (∀ i ≠ i0, g' i = g i) → ‖geometricMedian s g'‖ ≤ R) ∧
    (∃ g' : ℕ → W ι, (∀ i ≠ i0, g' i = g i) ∧ ‖empiricalMean s g'‖ > C) :=
  median_bounded_mean_unbounded_one_outlier_of_majority s g i0 hi0 h_maj C

/-- Test witness (threshold limit): for nonpositive Z thresholds, every coordinate
passes the mask test, so the filtered mean equals the ordinary empirical mean. -/
example (s : Finset ℕ) (g : ℕ → W ι) {z : ℝ} (hz : z ≤ 0) :
    zFilteredEmpiricalMean s g z = empiricalMean s g :=
  z_filtered_empirical_mean_eq_empirical_mean_of_nonpos_threshold s g hz

/-- Test witness (majority safety): both the median and filtered mean stay bounded
when a strict majority of points are fixed and outliers are bounded. -/
example (s s_fixed : Finset ℕ) (g : ℕ → W ι) (h_sub : s_fixed ⊆ s)
    (h_maj : 2 * s_fixed.card > s.card) (z R_fixed R_out : ℝ) (hs : s.Nonempty)
    (h_fixed_bound : ∀ i ∈ s_fixed, ‖g i‖ ≤ R_fixed) :
    ∃ R_med : ℝ, ∀ g' : ℕ → W ι, (∀ i ∈ s_fixed, g' i = g i) →
      (∀ i ∈ s \ s_fixed, ‖g' i‖ ≤ R_out) →
      ‖geometricMedian s g'‖ ≤ R_med ∧ ‖zFilteredEmpiricalMean s g' z‖ ≤ max R_fixed R_out :=
  median_and_zfiltered_mean_bounded_subset s g s_fixed h_sub h_maj z R_fixed R_out hs h_fixed_bound

end LeanSharp.Tests
