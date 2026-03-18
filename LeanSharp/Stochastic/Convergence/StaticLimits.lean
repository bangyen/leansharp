/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Convergence.LimitAssumes
import LeanSharp.Stochastic.Foundations.Integrability
import LeanSharp.Stochastic.Foundations.RobbinsMonro

/-!
# Structural Convergence Interface for ZSharp

This module provides the most automated end-to-end convergence theorems for
the ZSharp algorithm. It bridges the gap between low-level structural
assumptions (smoothness, variance, etc.) and high-level almost-sure
convergence results by leveraging the integrability derivations and
hypothesis promotion layers.

## Theorems

* `zsharp_robbins_monro_almost_sure_convergence_structural`.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- **End-to-end structural convergence**: this is the most automated interface
for ZSharp convergence. It derives integrability from structural properties
(smoothness, variance, etc.) and returns the almost-sure objective limit. -/
theorem zsharp_robbins_monro_almost_sure_convergence_structural
    (L_smooth : NNReal) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_struct : ZSharpStructuralAssumptions f w η z σsq)
    (h_rm : robbins_monro_stepsize η)
    (h_bridge : ∃ R : NNReal,
      StronglyAdapted ℱfil (fun t ω => f (w t ω))
        ∧ (∀ t, ℙ[fun ω => f (w (t + 1) ω) | ℱfil t] ≤ᵐ[ℙ] (fun ω => f (w t ω)))
        ∧ (∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R))
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_desc_step : ∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochastic_zsharp_step (w t ω') η t z
        (fun ω'' => gradient f (w t ω'')) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq) :
    (∀ T : ℕ,
      (∑ t ∈ Finset.range T, (η t / 4) * 𝔼[fun ω => ‖gradient f (w t ω)‖ ^ 2]) ≤
        𝔼[fun ω => f (w 0 ω)] - 𝔼[fun ω => f (w T ω)] +
        (∑ t ∈ Finset.range T, (η t ^ 2 * L_smooth / 2) * σsq))
      ∧ zsharp_objective_as_convergence f w := by
  exact zsharp_robbins_monro_almost_sure_convergence_of_model_descent_hypotheses
    L_smooth f w η z σsq ℱ ℱfil ⟨h_rm, ⟨h_struct⟩, h_bridge, h_meas, h_desc_step⟩

end LeanSharp
