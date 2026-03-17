/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Stochastic.MartingaleModel

/-!
# Robbins-Monro Martingale Interface Tests

This module verifies that the martingale-update interface composes correctly in
downstream theorem statements.

## Theorems

* `martingale_model_interface_test`.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {Ω : Type*} [MeasureSpace Ω]

/-- **Martingale Model Interface Verification**: Ensures a concrete
`robbins_monro_update_martingale_model` immediately provides both the stochastic
update recursion and the cumulative-noise martingale witness expected by
Robbins-Monro convergence proofs. -/
theorem martingale_model_interface_test
    (f : W (Fin 2) → ℝ)
    (w : ℕ → Ω → W (Fin 2))
    (η : ℕ → ℝ)
    (ℱ : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_model : robbins_monro_update_martingale_model f w η ℱ) :
    (∀ t, ∀ᵐ ω ∂ℙ,
      w (t + 1) ω =
        w t ω - η t • (gradient f (w t ω) + h_model.ξ t ω))
      ∧ Martingale (robbins_monro_partial_noise_sum h_model.ξ) ℱ ℙ := by
  exact ⟨
    robbins_monro_update_recursion f w η ℱ h_model,
    robbins_monro_noise_partial_sum_martingale f w η ℱ h_model
  ⟩

end LeanSharp
