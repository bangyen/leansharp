/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Stochastic.Foundations.Integrability
import LeanSharp.Stochastic.Foundations.RobbinsMonro

/-!
# Integrability Tests

This file verifies that the structural integrability derivations in
`LeanSharp.Stochastic.Integrability` correctly interface with the
Robbins-Monro convergence theorems.

## Examples

* `integrability_interface_test`.
-/

namespace LeanSharp.Tests

open ProbabilityTheory MeasureTheory

/-- **Structural Envelope Wiring Verification**: This test ensures the sequence
descent envelope can be instantiated from structural assumptions by deriving
integrability through `zsharp_structural_integrability`. -/
example
    {Ω : Type*}
    [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    (L_smooth : NNReal) (f : W (Fin 2) → ℝ)
    (w : ℕ → Ω → W (Fin 2)) (η : ℕ → ℝ) (z σsq : ℝ) (T : ℕ)
    (ℱ : ℕ → MeasurableSpace Ω)
    (h_struct : ZSharpStructuralAssumptions f w η z σsq)
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_desc_step : ∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochasticZSharpStep (w t ω') η t z
        (fun ω'' => gradient f (w t ω'')) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq) :
    (∑ t ∈ Finset.range T, (η t / 4) * 𝔼[fun ω => ‖gradient f (w t ω)‖ ^ 2]) ≤
      𝔼[fun ω => f (w 0 ω)] - 𝔼[fun ω => f (w T ω)] +
      (∑ t ∈ Finset.range T, (η t ^ 2 * L_smooth / 2) * σsq) := by
  have h_int_all := zsharp_structural_integrability f w η z σsq h_struct
  exact stochastic_zsharp_sequence_descent L_smooth f w η z σsq T
    (fun t ω => gradient f (w t ω)) ℱ (fun t => h_struct.h_step t) h_desc_step
    h_int_all.1 h_int_all.2 h_meas

/-- **Integrability Verification**: This "test" ensures that the structural
hypothesis bundle can be instantiated and used to state a convergence result
without manually providing integrability for every iterate. -/
example
    {Ω : Type*}
    [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    (L_smooth : NNReal) (f : W (Fin 2) → ℝ)
    (w : ℕ → Ω → W (Fin 2)) (η : ℕ → ℝ) (z σsq : ℝ)
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_struct : ZSharpStructuralAssumptions f w η z σsq)
    (h_rm : RobbinsMonroStepsize η)
    (h_bridge : ∃ R : NNReal,
      StronglyAdapted ℱfil (fun t ω => f (w t ω))
        ∧ (∀ t, ℙ[fun ω => f (w (t + 1) ω) | ℱfil t] ≤ᵐ[ℙ] (fun ω => f (w t ω)))
        ∧ (∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R))
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_desc_step : ∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochasticZSharpStep (w t ω') η t z
        (fun ω'' => gradient f (w t ω'')) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq) :
    ZSharpObjectiveAsConvergence f w := by
  -- This should now be a one-liner call to the structural interface
  exact (zsharp_robbins_monro_almost_sure_convergence_of_model_descent_hypotheses
    L_smooth f w η z σsq ℱ ℱfil
    ⟨h_rm, ⟨h_struct⟩, h_bridge, h_meas, h_desc_step⟩).2

end LeanSharp.Tests
