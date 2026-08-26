/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Core.Filters
import LeanSharp.Core.TailFilters
import LeanSharp.Theory.Concentration
import LeanSharp.Theory.Dynamics.Convergence

/-!
# ZSharp Perturbation Tests

This module exists to verify that the paper-faithful ZSharp ascent step
(arXiv:2505.02369), which is computed from the *filtered* gradient rather than
the raw one, satisfies the radius bound and degenerates to the ordinary SAM
perturbation exactly in the paper's fallback case.

## Examples

* `test_norm_zsharpPerturbation_le_interface`.
* `test_zsharpPerturbation_fallback_interface`.
* `test_zsharpPerturbation_fallback_reachable`.
* `test_zsharpPerturbation_eq_filtered_direction`.
* `test_zsharpStep_descends_along_raw_gradient`.
* `test_tail_filter_decomposition_interface`.
* `test_tail_filter_contraction_interface`.
* `test_tail_filter_sparsity_interface`.
-/

namespace LeanSharp.Tests

variable {ι : Type*} [Fintype ι]

/-- Interface test: the ZSharp perturbation stays inside the radius-`ρ` ball,
matching the guarantee the SAM perturbation provides. -/
example (L : W ι → ℝ) (w : W ι) (ρ z : ℝ) (hρ : 0 ≤ ρ) :
    ‖zsharpPerturbation L w ρ z‖ ≤ ρ :=
  norm_zsharpPerturbation_le L w ρ z hρ

/-- Interface test: when the tail filter annihilates the gradient, the ZSharp
perturbation falls back to the ordinary SAM perturbation, as in the paper's
second case. -/
example (L : W ι → ℝ) (w : W ι) (ρ z : ℝ)
    (h_zero : ‖tailFilteredGradient (gradient L w) z‖ = 0) :
    zsharpPerturbation L w ρ z = samPerturbation L w ρ :=
  zsharpPerturbation_eq_samPerturbation_of_tail_zero L w ρ z h_zero

/-- Interface test: the fallback is reachable — a constant gradient has no outliers,
so the tail filter zeroes it and the step degenerates to SAM. -/
example [Nonempty ι] (L : W ι → ℝ) (w : W ι) (ρ z : ℝ)
    (h_std : vectorStd (gradient L w) = 0) :
    zsharpPerturbation L w ρ z = samPerturbation L w ρ :=
  zsharpPerturbation_eq_samPerturbation_of_std_zero L w ρ z h_std

/-- In the non-degenerate case the ascent step points along the *tail-filtered*
gradient, which is the substance of the paper's definition: filtering steers the
perturbation onto the largest-|Z-score| components. -/
example (L : W ι → ℝ) (w : W ι) (ρ z : ℝ)
    (h_pos : ‖tailFilteredGradient (gradient L w) z‖ ≠ 0) :
    zsharpPerturbation L w ρ z =
      (ρ / ‖tailFilteredGradient (gradient L w) z‖) • tailFilteredGradient (gradient L w) z := by
  simp only [zsharpPerturbation, h_pos, ite_false]

/-- The ZSharp update step descends along the *raw* gradient at the point displaced by
the filtered-gradient ascent step: per the paper, only the ascent step is filtered. -/
example (L : W ι → ℝ) (w : W ι) (η : ℕ → ℝ) (t : ℕ) (ρ z : ℝ) :
    zsharpStep L w η t ρ z = w - (η t) • gradient L (w + zsharpPerturbation L w ρ z) :=
  rfl

/-- Interface test: the paper's tail filter and the repo's inlier filter decompose the
gradient exactly, so the two are genuine complements rather than variants. -/
example (g : W ι) (z : ℝ) :
    tailFilteredGradient g z + filteredGradient g z = g :=
  tail_filtered_add_filtered g z

/-- Interface test: the tail filter is an `L₂` contraction, matching the inlier filter's
`norm_filtered_gradient_le`. -/
example (g : W ι) (z : ℝ) : ‖tailFilteredGradient g z‖ ≤ ‖g‖ :=
  norm_tail_filtered_gradient_le g z

/-- Interface test: the paper's filter is sparsifying — it keeps at most a `1/z²`
fraction of components, the dual of `zScoreMask_coverage`. -/
example [Nonempty ι] (g : W ι) {z : ℝ} (hz : 0 < z) (hvar : vectorVariance g > 0) :
    ((Finset.univ.filter fun i =>
      ¬ |(WithLp.equiv 2 (ι → ℝ) g) i - vectorMean g| ≤ z * vectorStd g).card : ℝ)
        / (Fintype.card ι : ℝ) ≤ 1 / z^2 :=
  zScoreTailMask_sparsity g hz hvar

end LeanSharp.Tests
