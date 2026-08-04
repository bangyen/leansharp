/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Convergence.Process.SamDescent
import Mathlib.Probability.Process.Adapted

/-!
# Conditional SAM Oracle Model

This module defines the minimal filtration-level oracle contract for deriving
SAM descent envelopes. It deliberately does not model datasets, minibatches, or
architecture-specific randomness.

## Definitions
* `SAMConditionalOracle`: adapted SAM iterates with martingale noise.

## Theorems
This module defines the oracle contract; envelope derivations use it downstream.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- **Conditional SAM oracle contract**: the adversarial gradient decomposes into
the gradient at the SAM-perturbed iterate plus conditionally centered noise with
bounded conditional second moment. -/
structure SAMConditionalOracle
    (f : W ι → ℝ) (w : ℕ → Ω → W ι) (z ρ σsq : ℝ)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace) where
  /-- The stochastic adversarial gradient supplied to the update. -/
  g_adv : ℕ → Ω → W ι
  /-- The martingale-noise process in the oracle decomposition. -/
  noise : ℕ → Ω → W ι
  /-- Pointwise decomposition at the SAM-perturbed iterate. -/
  decomposition : ∀ t ω,
    g_adv t ω = gradient f (w t ω + samPerturbation f (w t ω) ρ) + noise t ω
  /-- The iterate process is adapted to the filtration. -/
  adapted : StronglyAdapted ℱfil w
  /-- Each noise increment is integrable. -/
  noise_integrable : ∀ t, Integrable (noise t) ℙ
  /-- Noise is conditionally centered. -/
  noise_cond_mean : ∀ t,
    ℙ[noise t | ℱfil t] =ᵐ[ℙ] (fun _ => 0)
  /-- Conditional noise second moment is bounded by `σsq`. -/
  noise_cond_var : ∀ t,
    ℙ[fun ω => ‖noise t ω‖ ^ 2 | ℱfil t] ≤ᵐ[ℙ] (fun _ => σsq)

end LeanSharp
