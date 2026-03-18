/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Convergence.Bridges
import LeanSharp.Stochastic.Foundations.Integrability

/-!
# Convergence Hypothesis Bundles

This module provides packaged hypothesis bundles for ZSharp objective
convergence. These bundles group Robbins-Monro step-size assumptions,
objective-bridge data, and sequence-descent envelope premises to
simplify interface theorems.

## Definitions

* `zsharp_objective_bridge_hypotheses`.
* `zsharp_strongest_descent_hypotheses`.
* `zsharp_model_descent_hypotheses`.

## Theorems

* `zsharp_strongest_descent_hypotheses_of_model_descent_hypotheses`.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- Strongest currently exposed ZSharp descent hypothesis bundle for objective
limits. -/
def zsharp_strongest_descent_hypotheses
    (L_smooth : NNReal) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace) : Prop :=
  robbins_monro_stepsize η
    ∧ (∃ R : NNReal,
    StronglyAdapted ℱfil (fun t ω => f (w t ω))
      ∧ (∀ t, ℙ[fun ω => f (w (t + 1) ω) | ℱfil t] ≤ᵐ[ℙ] (fun ω => f (w t ω)))
      ∧ (∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R))
    ∧ (∀ t, ∀ᵐ ω ∂ℙ, w (t + 1) ω = stochastic_zsharp_step (w t ω) η t z (g_adv t) ω)
    ∧ (∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochastic_zsharp_step (w t ω') η t z (g_adv t) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq)
    ∧ (∀ t, Integrable (fun ω => f (w t ω)) ℙ)
    ∧ (∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2) ℙ)
    ∧ (∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)

/-- Concrete model-level hypothesis bundle for ZSharp objective convergence -/
def zsharp_model_descent_hypotheses
    (L_smooth : NNReal) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace) : Prop :=
  robbins_monro_stepsize η
    ∧ Nonempty (ZSharpStructuralAssumptions f w η z σsq)
    ∧ (∃ R : NNReal,
    StronglyAdapted ℱfil (fun t ω => f (w t ω))
      ∧ (∀ t, ℙ[fun ω => f (w (t + 1) ω) | ℱfil t] ≤ᵐ[ℙ] (fun ω => f (w t ω)))
      ∧ (∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R))
    ∧ (∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    ∧ (∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochastic_zsharp_step (w t ω') η t z
        (fun ω'' => gradient f (w t ω'')) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq)

omit [IsProbabilityMeasure (volume : Measure Ω)] in
/-- Repackages concrete model-level ZSharp hypotheses into the strongest descent
bundle used by downstream interface theorems. -/
theorem zsharp_strongest_descent_hypotheses_of_model_descent_hypotheses
    (L_smooth : NNReal) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_model :
      zsharp_model_descent_hypotheses L_smooth f w η z σsq ℱ ℱfil) :
    zsharp_strongest_descent_hypotheses L_smooth f w η z σsq
      (fun t ω => gradient f (w t ω)) ℱ ℱfil := by
  rcases h_model with ⟨h_rm, ⟨h_struct⟩, h_bridge, h_meas, h_desc_step⟩
  have h_int_all := zsharp_structural_integrability f w η z σsq h_struct
  exact ⟨h_rm, h_bridge, h_struct.h_step, h_desc_step, h_int_all.1, h_int_all.2, h_meas⟩

end LeanSharp
