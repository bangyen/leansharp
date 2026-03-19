/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Theory.Structural.HardThresholding
import LeanSharp.Theory.Structural.StabilityProperties

/-!
# Structural Stability Tests

This module exists to verify that hard-thresholding and filtered-update
stability theorems remain directly consumable by downstream proof modules.

## Examples

* `test_hard_threshold_scalar_not_lipschitz_interface`.
* `test_localized_filtered_update_norm_bound_interface`.
* `test_uniform_filtered_process_stability_interface`.
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

end LeanSharp.Tests
