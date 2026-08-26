/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Core.Filters
import LeanSharp.Core.LayerFilters
import LeanSharp.Core.PercentileFilters
import LeanSharp.Core.Perturbation
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
* `test_zsharpPerturbation_eq_filtered_direction`.
* `test_zsharpStep_descends_along_raw_gradient`.
* `test_tail_filter_decomposition_interface`.
* `test_tail_filter_contraction_interface`.
* `test_tail_filter_sparsity_interface`.
* `test_layer_filter_const_reduction`.
* `test_layer_filter_contraction_interface`.
* `test_percentile_sparsity_interface`.
* `test_percentile_contraction_interface`.
-/

namespace LeanSharp.Tests

variable {ι : Type*} [Fintype ι] {Λ : Type*} [DecidableEq Λ]

/-- Interface test: the ZSharp perturbation stays inside the radius-`ρ` ball,
matching the guarantee the SAM perturbation provides. -/
example (L : W ι → ℝ) (w : W ι) (π : ι → Λ) (ρ Qp : ℝ) (hρ : 0 ≤ ρ) :
    ‖zsharpPerturbation L w π ρ Qp‖ ≤ ρ :=
  norm_zsharpPerturbation_le L w π ρ Qp hρ

/-- Interface test: when the percentile filter annihilates the gradient, the ZSharp
perturbation falls back to the ordinary SAM perturbation, as in the paper's
second case. -/
example (L : W ι → ℝ) (w : W ι) (π : ι → Λ) (ρ Qp : ℝ)
    (h_zero : ‖percentileFilteredGradient (gradient L w) π Qp‖ = 0) :
    zsharpPerturbation L w π ρ Qp = samPerturbation L w ρ :=
  zsharpPerturbation_eq_samPerturbation_of_filtered_zero L w π ρ Qp h_zero

/-- In the non-degenerate case the ascent step points along the *percentile-filtered*
gradient, which is the substance of the paper's definition: filtering steers the
perturbation onto the top `1 - Q_p` fraction of each layer. -/
example (L : W ι → ℝ) (w : W ι) (π : ι → Λ) (ρ Qp : ℝ)
    (h_pos : ‖percentileFilteredGradient (gradient L w) π Qp‖ ≠ 0) :
    zsharpPerturbation L w π ρ Qp =
      (ρ / ‖percentileFilteredGradient (gradient L w) π Qp‖) •
        percentileFilteredGradient (gradient L w) π Qp := by
  simp only [zsharpPerturbation, h_pos, ite_false]

/-- The ZSharp update step descends along the *raw* gradient at the point displaced by
the filtered-gradient ascent step: per the paper, only the ascent step is filtered. -/
example (L : W ι → ℝ) (w : W ι) (η : ℕ → ℝ) (t : ℕ) (π : ι → Λ) (ρ Qp : ℝ) :
    zsharpStep L w η t π ρ Qp =
      w - (η t) • gradient L (w + zsharpPerturbation L w π ρ Qp) :=
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

/-- Interface test: a constant partition is the single-layer case, so the layer-wise
filter collapses to the global tail filter. This is what lets the 2-D landscape tests
instantiate the partition trivially. -/
example (g : W ι) (z : ℝ) (l₀ : Λ) :
    layerTailFilteredGradient g (fun _ : ι => l₀) z = tailFilteredGradient g z :=
  layerTailFilteredGradient_const g z l₀

/-- Interface test: the layer-wise filter is an `L₂` contraction, so the chain-stability
style bounds carry over to per-layer statistics. -/
example (g : W ι) (π : ι → Λ) (z : ℝ) :
    ‖layerTailFilteredGradient g π z‖ ≤ ‖g‖ :=
  norm_layer_tail_filtered_gradient_le g π z

/-- Interface test: the percentile filter pins the retained *fraction* of each layer,
which is exactly what a fixed `z * σ` threshold cannot do. -/
example (g : W ι) (π : ι → Λ) {Qp : ℝ} (hQ1 : Qp ≤ 1) (l : Λ) :
    (keptCoords g π Qp l).card + ⌈Qp * ((fiber π l).card : ℝ)⌉₊
      ≤ (fiber π l).card :=
  percentile_mask_sparsity g π hQ1 l

/-- Interface test: the percentile filter is an `L₂` contraction. -/
example (g : W ι) (π : ι → Λ) (Qp : ℝ) :
    ‖percentileFilteredGradient g π Qp‖ ≤ ‖g‖ :=
  norm_percentile_filtered_gradient_le g π Qp

end LeanSharp.Tests
