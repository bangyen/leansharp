/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Theory.Structural.Stability

/-!
# Stability Interface Tests

This module verifies deterministic one-step stability interfaces used by the
roadmap's localized stability milestone.

## Theorems

* `localized_filtered_update_norm_bound_test`.
* `localized_filtered_update_norm_bound_of_reference_test`.
* `uniform_filtered_process_stability_test`.
-/

namespace LeanSharp

/-- **Localized Drift Interface Verification**: if the step gradient is bounded,
the filtered one-step update norm is bounded proportionally. -/
theorem localized_filtered_update_norm_bound_test
    {ι : Type*} [Fintype ι]
    (w g : W ι) (η z R : ℝ)
    (hη : 0 ≤ η) (hR : ‖g‖ ≤ R) :
    ‖(w - η • filtered_gradient g z) - w‖ ≤ η * R := by
  exact localized_filtered_update_norm_bound w g η z R hη hR

/-- **Reference-Based Drift Interface Verification**: if a gradient stays close
to a bounded reference gradient, the filtered update obeys the corresponding
localized bound. -/
theorem localized_filtered_update_norm_bound_of_reference_test
    {ι : Type*} [Fintype ι]
    (w g g_ref : W ι) (η z R_ref Δ : ℝ)
    (hη : 0 ≤ η)
    (h_ref : ‖g_ref‖ ≤ R_ref)
    (h_loc : ‖g - g_ref‖ ≤ Δ) :
    ‖(w - η • filtered_gradient g z) - w‖ ≤ η * (R_ref + Δ) := by
  exact localized_filtered_update_norm_bound_of_reference
    w g g_ref η z R_ref Δ hη h_ref h_loc

/-- **Uniform Stability Interface Verification**: checks the sequence-level
uniform deterministic stability theorem for filtered updates. -/
theorem uniform_filtered_process_stability_test
    {ι : Type*} [Fintype ι]
    (w : ℕ → W ι) (g : ℕ → W ι) (η : ℕ → ℝ) (z R : ℝ)
    (h_step : ∀ t, w (t + 1) = w t - η t • filtered_gradient (g t) z)
    (hη : ∀ t, 0 ≤ η t)
    (hR : ∀ t, ‖g t‖ ≤ R) :
    ∀ T : ℕ, ‖w T - w 0‖ ≤ Finset.sum (Finset.range T) (fun t => η t * R) := by
  exact uniform_filtered_process_stability w g η z R h_step hη hR

end LeanSharp
