/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Theory.Structural.HardThresholding

/-!
# Hard-Thresholding Interface Tests

This module verifies that hard-thresholding structural properties are available
through stable theorem interfaces.

## Theorems

* `hard_threshold_idempotent_interface_test`.
* `hard_threshold_non_lipschitz_interface_test`.
-/

namespace LeanSharp

/-- **Idempotence Interface Verification**: applying hard-thresholding twice is
the same as applying it once. -/
theorem hard_threshold_idempotent_interface_test
    {ι : Type*} (w : W ι) (τ : ℝ) :
    hard_threshold (hard_threshold w τ) τ = hard_threshold w τ := by
  exact hard_threshold_idempotent w τ

/-- **Non-Lipschitz Interface Verification**: scalar hard-thresholding with
positive threshold has no global Lipschitz constant. -/
theorem hard_threshold_non_lipschitz_interface_test
    (τ : ℝ) (hτ : 0 < τ) :
    ∀ K : NNReal, ¬ LipschitzWith K (fun x : ℝ => hard_threshold_scalar x τ) := by
  exact hard_threshold_scalar_not_lipschitz τ hτ

end LeanSharp
