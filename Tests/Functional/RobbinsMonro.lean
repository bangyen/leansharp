/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Stochastic.Foundations.Martingale
import LeanSharp.Stochastic.Foundations.RobbinsMonro
import LeanSharp.Stochastic.Foundations.Schedules.StronglyConvex

/-!
# Robbins-Monro Tests

This module verifies that the martingale-update interface composes correctly in
downstream theorem statements.

## Examples

* `bridge_contract_interface_test`.
-/

namespace LeanSharp.Tests

open ProbabilityTheory MeasureTheory

variable {Ω : Type*} [MeasureSpace Ω]

/-- **Martingale Model Interface Verification**: Ensures a concrete
`RobbinsMonroUpdateMartingaleModel` immediately provides both the stochastic
update recursion and the cumulative-noise martingale witness expected by
Robbins-Monro convergence proofs. -/
example (f : W (Fin 2) → ℝ)
    (w : ℕ → Ω → W (Fin 2))
    (η : ℕ → ℝ)
    (ℱ : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_model : RobbinsMonroUpdateMartingaleModel f w η ℱ) :
    (∀ t, ∀ᵐ ω ∂ℙ,
      w (t + 1) ω =
        w t ω - η t • (gradient f (w t ω) + h_model.ξ t ω))
      ∧ Martingale (robbinsMonroPartialNoiseSum h_model.ξ) ℱ ℙ := by
  exact ⟨h_model.h_update, h_model.h_noise_martingale⟩

/-- **Martingale-to-Objective-Limit Wiring Verification**: ensures the new
Robbins-Monro interface theorem accepts the martingale update model and returns
the update recursion and almost-sure objective convergence through focused
contracts. -/
example [IsProbabilityMeasure (volume : Measure Ω)]
    (f : W (Fin 2) → ℝ)
    (w : ℕ → Ω → W (Fin 2))
    (η : ℕ → ℝ)
    (ℱ : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_model : RobbinsMonroUpdateMartingaleModel f w η ℱ)
    (R : NNReal)
    (h_adapted : StronglyAdapted ℱ (fun t ω => f (w t ω)))
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ)
    (h_step :
      ∀ t, (fun ω => f (w t ω)) ≤ᵐ[ℙ] ℙ[fun ω => f (w (t + 1) ω) | ℱ t])
    (hbdd : ∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R) :
    (∀ t, ∀ᵐ ω ∂ℙ,
      w (t + 1) ω =
        w t ω - η t • (gradient f (w t ω) + h_model.ξ t ω))
      ∧ ZSharpObjectiveAsConvergence f w := by
  refine ⟨?_, ?_⟩
  · exact h_model.h_update
  · exact zsharp_robbins_monro_objective_limit_with_martingale_model
      f w ℱ R h_adapted h_int h_step hbdd

/-- **Concrete Weight-Sequence Interface Verification**: confirms that the
`weightSequence` specialization exposes both the explicit recursion identity and
the almost-sure objective convergence contracts for downstream callers. -/
example [IsProbabilityMeasure (volume : Measure Ω)]
    (L_smooth : NNReal) (f : W (Fin 2) → ℝ)
    (w0 : W (Fin 2)) (η : ℕ → ℝ) (z σsq : ℝ)
    (g_adv : ℕ → Ω → W (Fin 2))
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_model : ZSharpModelDescentHypotheses
      L_smooth f (weightSequence w0 η z g_adv) η z σsq ℱ ℱfil) :
    (∀ t, ∀ᵐ ω ∂ℙ,
      weightSequence w0 η z g_adv (t + 1) ω =
        stochasticZSharpStep (weightSequence w0 η z g_adv t ω) η t z (g_adv t) ω)
      ∧ ZSharpObjectiveAsConvergence f (weightSequence w0 η z g_adv) := by
  have h_result :=
    weight_sequence_robbins_monro_almost_sure_convergence_of_model_descent_hypotheses
      (L_smooth := L_smooth) (f := f) (w0 := w0)
      (η := η) (z := z) (σsq := σsq) (g_adv := g_adv) (ℱ := ℱ) (ℱfil := ℱfil) h_model
  exact ⟨h_result.1, h_result.2.2⟩

/-- **Bridge API Wiring Verification**: checks that the project-level bridge
contract wrappers remain directly usable from theorem clients. -/
example [IsProbabilityMeasure (volume : Measure Ω)]
    (f : W (Fin 2) → ℝ)
    (w : ℕ → Ω → W (Fin 2))
    (ℱ : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (R : NNReal)
    (h_sub : Submartingale (fun t ω => f (w t ω)) ℱ ℙ)
    (hbdd : ∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R) :
    ZSharpObjectiveAsConvergence f w := by
  exact zsharp_objective_as_convergence_of_submartingale_bridge_contract
    f w ℱ R h_sub hbdd

end LeanSharp.Tests
