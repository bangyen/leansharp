/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Stochastic.Integrability
import LeanSharp.Stochastic.StructuralConvergence

/-!
# Integrability Interface Tests
This file verifies that the structural integrability derivations in
`LeanSharp.Stochastic.Integrability` correctly interface with the
Robbins-Monro convergence theorems.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

/-- **Integrability Verification**: This "test" ensures that the structural
hypothesis bundle can be instantiated and used to state a convergence result
without manually providing integrability for every iterate. -/
theorem integrability_interface_test {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (L_smooth : ℝ) (f : W (Fin 2) → ℝ)
    (w : ℕ → Ω → W (Fin 2)) (η : ℕ → ℝ) (z σsq : ℝ)
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_L_pos : 0 ≤ L_smooth)
    (h_struct : ZSharpStructuralAssumptions f w η z σsq)
    (h_rm : robbins_monro_stepsize η)
    (h_bridge : ∃ R : NNReal,
      StronglyAdapted ℱfil (fun t ω => f (w t ω))
        ∧ (∀ t, ℙ[fun ω => f (w (t + 1) ω) | ℱfil t] ≤ᵐ[ℙ] (fun ω => f (w t ω)))
        ∧ (∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R))
    (h_desc_step : ∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochastic_zsharp_step (w t ω') η t z (fun ω'' => gradient f (w t ω'')) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq)
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ)
    (h_int_grad : ∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2) ℙ)
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace) :
    zsharp_objective_as_convergence f w := by
  -- This should now be a one-liner call to the structural interface
  exact zsharp_robbins_monro_objective_limit_structural
    L_smooth f w η z σsq ℱ ℱfil h_L_pos h_struct h_rm h_bridge
    h_desc_step h_int h_int_grad h_meas

end LeanSharp
