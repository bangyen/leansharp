/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Robustness.MedianComparison
import LeanSharp.Theory.Structural.FilterAlgebra

/-!
# Robustness Comparison Results

This module exists to collect high-level comparison theorems that combine core
median and mean robustness lemmas into user-facing statements.

## Theorems

* `median_bounded_mean_unbounded_one_outlier_of_majority`.
* `median_and_zfiltered_mean_bounded_subset`.
* `z_filtered_empirical_mean_eq_empirical_mean_of_nonpos_threshold`.
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
    (C : ℝ) (hC : -1 ≤ C) :
    (∃ R : ℝ, ∀ g' : α → W ι, (∀ i ≠ i0, g' i = g i) →
        ‖geometric_median s g'‖ ≤ R) ∧
    (∃ g' : α → W ι, (∀ i ≠ i0, g' i = g i) ∧ ‖empirical_mean s g'‖ > C) := by
  classical
  constructor
  · obtain ⟨R, hR⟩ := median_bounded_subset s g (s.erase i0) (Finset.erase_subset i0 s) h_maj
    refine ⟨R, fun g' hg' => hR g' (fun i hi => hg' i (Finset.mem_erase.1 hi).1)⟩
  · exact mean_unbounded s g i0 hi0 C hC

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
      ‖geometric_median s g'‖ ≤ R_med
        ∧ ‖z_filtered_empirical_mean s g' z‖ ≤ max R_fixed R_out := by
  obtain ⟨R_med, h_med⟩ := median_bounded_subset s g s_fixed h_sub h_maj
  refine ⟨R_med, ?_⟩
  intro g' hg_fixed hg_out
  refine ⟨h_med g' hg_fixed, ?_⟩
  exact z_filtered_empirical_mean_bounded_subset_max
    s g s_fixed h_sub z R_fixed R_out hs h_fixed_bound g' hg_fixed hg_out

/-- **Degenerate-threshold identity**: for nonpositive Z thresholds, every coordinate
passes the mask test, so the filtered empirical mean equals the ordinary empirical mean.
This theorem exists to expose the exact regime where filtered aggregation reduces to
the classical mean and therefore inherits its robustness profile. -/
@[simp] theorem z_filtered_empirical_mean_eq_empirical_mean_of_nonpos_threshold
    (s : Finset α) (g : α → W ι) {z : ℝ} (hz : z ≤ 0) :
    z_filtered_empirical_mean s g z = empirical_mean s g := by
  unfold z_filtered_empirical_mean
  congr 1
  funext i
  apply (WithLp.equiv 2 (ι → ℝ)).injective
  ext j
  apply filtered_gradient_coord_preservation
  unfold z_score_mask
  rw [Equiv.apply_symm_apply]
  have h_keep : |(WithLp.equiv 2 (ι → ℝ) (g i)) j - vector_mean (g i)| ≥ z * vector_std (g i) := by
    have hzσ : z * vector_std (g i) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hz (Real.sqrt_nonneg _)
    exact le_trans hzσ (abs_nonneg _)
  exact by simpa only [
    WithLp.equiv_apply,
    ge_iff_le,
    ite_eq_left_iff,
    not_le,
    zero_ne_one,
    imp_false,
    not_lt
  ] using h_keep

end LeanSharp
