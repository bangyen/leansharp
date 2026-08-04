/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Core.Filters
import LeanSharp.Theory.Concentration
import LeanSharp.Theory.Structural.ChainStability
import LeanSharp.Theory.Structural.FilterAlgebra
import LeanSharp.Theory.Structural.HardThresholding
import LeanSharp.Theory.Structural.StabilityProperties

/-!
# Structural Stability Tests

This module exists to verify that hard-thresholding, filtered-update
stability, and filter-characterization theorems remain directly consumable
by downstream proof modules.

## Examples

* `test_hard_threshold_scalar_not_lipschitz_interface`.
* `test_localized_filtered_update_norm_bound_interface`.
* `test_uniform_filtered_process_stability_interface`.
* `test_z_score_mask_scale_invariance_interface`.
* `test_zscore_mask_idempotent_interface`.
* `test_zscore_mask_nonempty_interface`.
* `test_filtered_gradient_std_zero_interface`.
* `test_single_outlier_extraction_interface`.
* `test_zsharp_chain_stability_interface`.
-/

namespace LeanSharp.Tests

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Interface test: the non-Lipschitz hard-thresholding theorem is callable with
an arbitrary Lipschitz constant witness. -/
example (τ : ℝ) (hτ : 0 < τ) (K : NNReal) :
    ¬ LipschitzWith K (fun x : ℝ => hardThresholdScalar x τ) := by
  exact (hard_threshold_scalar_not_lipschitz τ hτ) K

/-- Interface test: one-step localized stability bound can be consumed directly
as a per-step drift certificate. -/
example (w g : W ι) (η z R : ℝ)
    (hR : ‖g‖ ≤ R) :
    ‖(w - η • filteredGradient g z) - w‖ ≤ |η| * R := by
  exact localized_filtered_update_norm_bound w g η z R hR

/-- Interface test: the uniform filtered-process stability theorem is available
for sequence-level deterministic stability arguments. -/
example (w : ℕ → W ι) (g : ℕ → W ι) (η : ℕ → ℝ) (z R : ℝ)
    (h_step : ∀ t, w (t + 1) = w t - η t • filteredGradient (g t) z)
    (hR : ∀ t, ‖g t‖ ≤ R) :
    ∀ T : ℕ, ‖w T - w 0‖ ≤ Finset.sum (Finset.range T) (fun t => |η t| * R) := by
  exact uniform_filtered_process_stability w g η z R h_step hR

/-- Interface test: the Z-score mask is invariant under global gradient scaling,
so the algorithm's behavior is scale-agnostic. -/
example (g : W ι) (z : ℝ) {k : ℝ} (hk : k ≠ 0) :
    zScoreMask (k • g) z = zScoreMask g z :=
  z_score_mask_scale_invariance g z hk

/-- Interface test: the Z-score mask is idempotent under the Hadamard product. -/
example (g : W ι) (z : ℝ) :
    hadamard (zScoreMask g z) (zScoreMask g z) = zScoreMask g z :=
  zscore_mask_idempotent g z

/-- Interface test: for $z \ge 1$, the filter always preserves at least one
component of the gradient. -/
example [Nonempty ι] (g : W ι) {z : ℝ} (hz_ge : 1 ≤ z) :
    ∃ i : ι, (WithLp.equiv 2 (ι → ℝ) (zScoreMask g z)) i = 1 :=
  zscore_mask_nonempty g hz_ge

/-- Interface test: the corrected mask keeps at least `1 - 1/z²` of the components
(those within `zσ` of the mean), discarding at most the Chebyshev tail fraction. -/
example [Nonempty ι] (g : W ι) {z : ℝ} (hz : 0 < z) (hvar : vectorVariance g > 0) :
    (1 - 1 / z^2) ≤
      ((Finset.univ.filter fun i =>
        |(WithLp.equiv 2 (ι → ℝ) g) i - vectorMean g| ≤ z * vectorStd g).card : ℝ)
        / (Fintype.card ι : ℝ) :=
  zScoreMask_coverage g hz hvar

/-- Interface test: constant gradients (zero standard deviation) are preserved
by the filter. -/
example [Nonempty ι] (g : W ι) (z : ℝ) (h_std : vectorStd g = 0) :
    filteredGradient g z = g :=
  filtered_gradient_eq_self_of_std_zero g z h_std

/-- Interface test: with a single outlier and zero mean, the filtered gradient
zeroes that outlier and preserves every inlier. -/
example (g : W ι) (z : ℝ) (i : ι) [DecidableEq ι]
    (h_μ : vectorMean g = 0)
    (h_outlier : z * vectorStd g < |(WithLp.equiv 2 (ι → ℝ) g) i|)
    (h_others : ∀ j : ι, j ≠ i → |(WithLp.equiv 2 (ι → ℝ) g) j| ≤ z * vectorStd g) :
    filteredGradient g z = (WithLp.equiv 2 (ι → ℝ)).symm
      (fun j => if j = i then 0 else (WithLp.equiv 2 (ι → ℝ) g) j) :=
  single_outlier_extraction g z i h_μ h_outlier h_others

/-- Interface test: layer-wise Z-score filtering bounds the total chain update
norm by the norm of the raw backpropagation gradients. -/
example {In Out : Type} {c : Chain In Out}
    (z : ℝ) (p : ChainData c) (x : In) (g_out : Out) :
    chainDataNormSq (backpropChain z p x g_out).1 ≤
    chainDataNormSq (rawBackpropChain p x g_out).1 :=
  zsharp_chain_stability z p x g_out

end LeanSharp.Tests
