/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Robustness.MedianComparison.Breakdown
import LeanSharp.Theory.Structural.FilterAlgebra

/-!
# Robustness Comparison Results

This module exists to collect high-level comparison theorems that combine core
median and mean robustness lemmas into user-facing statements.

## Theorems

* `median_bounded_mean_unbounded_one_outlier_of_majority`.
* `median_and_zfiltered_mean_bounded_subset`.
* `filtered_gradient_eq_zero_of_neg_threshold`.
-/

namespace LeanSharp

variable {ι : Type*} [Fintype ι]
variable {α : Type*}

/-- **One-outlier comparison (majority form)**: with a single movable point and a strict
majority of fixed points (`s \\ {i0}`), the empirical mean can be made arbitrarily large
while the geometric median stays bounded. This theorem exists as the minimal-assumption
form of the one-outlier robustness separation. -/
theorem median_bounded_mean_unbounded_one_outlier_of_majority [Nonempty ι]
    [DecidableEq α]
    (s : Finset α) (g : α → W ι)
    (i0 : α) (hi0 : i0 ∈ s)
    (h_maj : 2 * (s.erase i0).card > s.card)
    (C : ℝ) :
    (∃ R : ℝ, ∀ g' : α → W ι, (∀ i ≠ i0, g' i = g i) →
        ‖geometricMedian s g'‖ ≤ R) ∧
    (∃ g' : α → W ι, (∀ i ≠ i0, g' i = g i) ∧ ‖empiricalMean s g'‖ > C) := by
  classical
  constructor
  · obtain ⟨R, hR⟩ := median_bounded_subset s g (s.erase i0) (Finset.erase_subset i0 s) h_maj
    refine ⟨R, fun g' hg' => hR g' (fun i hi => hg' i (Finset.mem_erase.1 hi).1)⟩
  · exact mean_unbounded s g i0 hi0 C

/-- **Corollary (bounded-outlier regime certificate)**: when a strict majority of points are fixed
and outliers are norm-bounded, both the geometric median and the Z-filtered empirical
mean stay bounded. This theorem formalizes when filtered-mean aggregation is safe while
retaining a median-based fallback guarantee. -/
theorem median_and_zfiltered_mean_bounded_subset
    [DecidableEq α]
    (s : Finset α) (g : α → W ι)
    (s_fixed : Finset α) (h_sub : s_fixed ⊆ s) (h_maj : 2 * s_fixed.card > s.card)
    (z R_fixed R_out : ℝ) (hs : s.Nonempty)
    (h_fixed_bound : ∀ i ∈ s_fixed, ‖g i‖ ≤ R_fixed) :
    ∃ R_med : ℝ, ∀ g' : α → W ι, (∀ i ∈ s_fixed, g' i = g i) →
      (∀ i ∈ s \ s_fixed, ‖g' i‖ ≤ R_out) →
      ‖geometricMedian s g'‖ ≤ R_med
        ∧ ‖zFilteredEmpiricalMean s g' z‖ ≤ max R_fixed R_out := by
  obtain ⟨R_med, h_med⟩ := median_bounded_subset s g s_fixed h_sub h_maj
  refine ⟨R_med, ?_⟩
  intro g' hg_fixed hg_out
  refine ⟨h_med g' hg_fixed, ?_⟩
  let S : RobustSample α ι := {
    s := s,
    g := g,
    s_fixed := s_fixed,
    h_sub := h_sub,
    R_fixed := R_fixed,
    R_out := R_out,
    h_fixed_bound := h_fixed_bound
  }
  exact z_filtered_empirical_mean_bounded_subset_max S z hs g' hg_fixed hg_out

/-- **Negative-threshold zeroing**: for a strictly negative Z threshold and a
non-constant gradient, every component is an outlier, so the filter zeroes the
entire gradient. -/
theorem filtered_gradient_eq_zero_of_neg_threshold (g : W ι) {z : ℝ} (hz : z < 0)
    (hσ : vectorStd g ≠ 0) :
    filteredGradient g z = 0 := by
  unfold filteredGradient hadamard zScoreMask
  apply (WithLp.equiv 2 (ι → ℝ)).injective
  ext j
  have hσ_pos : 0 < vectorStd g :=
    lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hσ)
  have hzσ : z * vectorStd g < 0 := mul_neg_of_neg_of_pos hz hσ_pos
  have h_not : ¬ |g.ofLp j - vectorMean g| ≤ z * vectorStd g := by
    intro h
    have h_abs_nonneg : 0 ≤ |g.ofLp j - vectorMean g| := abs_nonneg _
    linarith
  simp only [Equiv.apply_symm_apply, WithLp.equiv_apply]
  rw [if_neg h_not, mul_zero]
  rfl

end LeanSharp
