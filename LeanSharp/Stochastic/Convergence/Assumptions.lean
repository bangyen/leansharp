/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Convergence.Bridges
import LeanSharp.Stochastic.Foundations.Integrability
import LeanSharp.Stochastic.Foundations.Oracles

/-!
# Convergence Hypothesis Bundles

This module provides packaged hypothesis bundles for ZSharp objective
convergence. These bundles group Robbins-Monro step-size assumptions,
objective-bridge data, and sequence-descent envelope premises to
simplify interface theorems.

## Definitions

* `zsharp_objective_bridge_hypotheses`.
* `ZSharpStrongestDescentHypotheses`.
* `ZSharpModelDescentHypotheses`.

## Theorems

This module only defines hypothesis bundles.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- Strongest currently exposed ZSharp descent hypothesis bundle for objective
limits. -/
def ZSharpStrongestDescentHypotheses
    (L_smooth : NNReal) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace) : Prop :=
  RobbinsMonroStepsize η
    ∧ (∃ R : NNReal,
    StronglyAdapted ℱfil (fun t ω => f (w t ω))
      ∧ (∀ t, ℙ[fun ω => f (w (t + 1) ω) | ℱfil t] ≤ᵐ[ℙ] (fun ω => f (w t ω)))
      ∧ (∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R))
    ∧ (∀ t, ∀ᵐ ω ∂ℙ, w (t + 1) ω = stochasticZSharpStep (w t ω) η t z (g_adv t) ω)
    ∧ (∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochasticZSharpStep (w t ω') η t z (g_adv t) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq)
    ∧ (∀ t, Integrable (fun ω => f (w t ω)) ℙ)
    ∧ (∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2) ℙ)
    ∧ (∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)

/-- Concrete model-level hypothesis bundle for ZSharp objective convergence -/
def ZSharpModelDescentHypotheses
    (L_smooth : NNReal) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace) : Prop :=
  RobbinsMonroStepsize η
    ∧ Nonempty (ZSharpStructuralAssumptions f w η z σsq)
    ∧ (∃ R : NNReal,
    StronglyAdapted ℱfil (fun t ω => f (w t ω))
      ∧ (∀ t, ℙ[fun ω => f (w (t + 1) ω) | ℱfil t] ≤ᵐ[ℙ] (fun ω => f (w t ω)))
      ∧ (∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R))
    ∧ (∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    ∧ (∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochasticZSharpStep (w t ω') η t z
        (fun ω'' => gradient f (w t ω'')) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq)

/-- Objective convergence hypothesis bundle for heavy-tailed (oracle-based) noise.
This bundle replaces the bounded-variance assumption with a polynomial-tail
certificate from a probability oracle. -/
def ZSharpOracleDescentHypotheses
    (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ)
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace) : Prop :=
  RobbinsMonroStepsize η
    ∧ (∃ C p : ℝ, 0 < C ∧ 1 ≤ p ∧
      NonGaussianProbabilityOracleProcess (fun t ω => w (t + 1) ω - w t ω))
    ∧ (∃ R : NNReal,
    StronglyAdapted ℱfil (fun t ω => f (w t ω))
      ∧ (∀ t, ℙ[fun ω => f (w (t + 1) ω) | ℱfil t] ≤ᵐ[ℙ] (fun ω => f (w t ω)))
      ∧ (∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R))
    ∧ (∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)

end LeanSharp
