/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Stochastic.Foundations.MartingaleOps
import LeanSharp.Stochastic.Foundations.RobbinsMonro

/-!
# Robbins-Monro Martingale Interface Tests

This module verifies that the martingale-update interface composes correctly in
downstream theorem statements.

## Theorems

* `martingale_model_interface_test`.
* `martingale_model_objective_limit_interface_test`.
* `model_descent_almost_sure_interface_test`.
* `objective_martingale_convergence_interface_test`.
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

/-- **Martingale-to-Objective-Limit Wiring Verification**: ensures the new
Robbins-Monro interface theorem accepts the martingale update model and returns
both update recursion and almost-sure objective convergence in one contract. -/
theorem martingale_model_objective_limit_interface_test
    [IsProbabilityMeasure (volume : Measure Ω)]
    (f : W (Fin 2) → ℝ)
    (w : ℕ → Ω → W (Fin 2))
    (η : ℕ → ℝ)
    (ℱ : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (hη : robbins_monro_stepsize η)
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
  exact zsharp_robbins_monro_objective_limit_with_martingale_model
    f w η ℱ hη h_model R h_adapted h_int h_step hbdd

/-- **Model-Descent Almost-Sure Interface Verification**: ensures the model-level
descent hypothesis bundle can directly produce the Robbins-Monro envelope plus
almost-sure objective convergence pair. -/
theorem model_descent_almost_sure_interface_test
    [IsProbabilityMeasure (volume : Measure Ω)]
    (L_smooth : NNReal)
    (f : W (Fin 2) → ℝ)
    (w : ℕ → Ω → W (Fin 2))
    (η : ℕ → ℝ)
    (z σsq : ℝ)
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_model : zsharp_model_descent_hypotheses L_smooth f w η z σsq ℱ ℱfil) :
    (∀ T : ℕ,
      (∑ t ∈ Finset.range T, (η t / 4) * 𝔼[fun ω => ‖gradient f (w t ω)‖ ^ 2]) ≤
        𝔼[fun ω => f (w 0 ω)] - 𝔼[fun ω => f (w T ω)] +
        (∑ t ∈ Finset.range T, (η t ^ 2 * L_smooth / 2) * σsq))
      ∧ zsharp_objective_as_convergence f w := by
  exact zsharp_robbins_monro_almost_sure_convergence_of_model_descent_hypotheses
    L_smooth f w η z σsq ℱ ℱfil h_model

/-- **Objective Martingale Convergence Interface Verification**: checks that the
Mathlib-backed martingale convergence wrapper can be applied directly when the
objective process is provided as a martingale with a uniform `L¹` bound. -/
theorem objective_martingale_convergence_interface_test
    [IsProbabilityMeasure (volume : Measure Ω)]
    (f : W (Fin 2) → ℝ)
    (w : ℕ → Ω → W (Fin 2))
    (ℱ : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_mart : Martingale (fun t ω => f (w t ω)) ℱ ℙ)
    (R : NNReal)
    (hbdd : ∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R) :
    zsharp_objective_as_convergence f w := by
  exact zsharp_objective_as_convergence_of_martingale f w ℱ R h_mart hbdd

end LeanSharp
