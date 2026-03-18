/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Stochastic.Foundations.Martingale
import LeanSharp.Stochastic.Foundations.RobbinsMonro

/-!
# Robbins-Monro Martingale Interface Tests

This module verifies that the martingale-update interface composes correctly in
downstream theorem statements.

## Theorems

* `martingale_model_interface_test`.
* `martingale_model_objective_limit_interface_test`.
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
  exact ⟨h_model.h_update, h_model.h_noise_martingale⟩

/-- **Martingale-to-Objective-Limit Wiring Verification**: ensures the new
Robbins-Monro interface theorem accepts the martingale update model and returns
the update recursion and almost-sure objective convergence through focused
contracts. -/
theorem martingale_model_objective_limit_interface_test
    [IsProbabilityMeasure (volume : Measure Ω)]
    (f : W (Fin 2) → ℝ)
    (w : ℕ → Ω → W (Fin 2))
    (η : ℕ → ℝ)
    (ℱ : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_model : robbins_monro_update_martingale_model f w η ℱ)
    (R : NNReal)
    (h_adapted : StronglyAdapted ℱ (fun t ω => f (w t ω)))
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ)
    (h_step :
      ∀ t, (fun ω => f (w t ω)) ≤ᵐ[ℙ] ℙ[fun ω => f (w (t + 1) ω) | ℱ t])
    (hbdd : ∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R) :
    (∀ t, ∀ᵐ ω ∂ℙ,
      w (t + 1) ω =
        w t ω - η t • (gradient f (w t ω) + h_model.ξ t ω))
      ∧ zsharp_objective_as_convergence f w := by
  refine ⟨?_, ?_⟩
  · exact h_model.h_update
  · exact zsharp_robbins_monro_objective_limit_with_martingale_model
      f w ℱ R h_adapted h_int h_step hbdd

end LeanSharp
