/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Convergence.HeavyTail
import LeanSharp.Stochastic.Foundations.Oracles

/-!
# Heavy-Tail Convergence Tests

This module verifies the wiring of almost-sure convergence under non-Gaussian,
heavy-tailed noise.

## Examples

* `cauchy_process_convergence_test`.
-/

namespace LeanSharp.Tests

open ProbabilityTheory MeasureTheory NNReal

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- **Cauchy Noise Test Witness**:
A simulated process that satisfies the `NonGaussianProbabilityOracle`.
This test verifies the wiring of almost-sure convergence. -/
example (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ)
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_oracle : ZSharpOracleDescentHypotheses f w η ℱ ℱfil)
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ) :
    ZSharpObjectiveAsConvergence f w := by
  apply zsharp_heavy_tail_convergence f w η ℱ ℱfil h_oracle h_int

/-- **Alpha-stable Noise Test Witness**: an α-stable oracle (α ≥ 1) is a valid
non-Gaussian oracle, so almost-sure convergence holds under α-stable increments. -/
example (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ)
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (α : ℝ) (h_alpha : 1 ≤ α)
    (h_rm : RobbinsMonroStepsize η)
    (h_stable : AlphaStableProbabilityOracleProcess
      (fun t ω => w (t + 1) ω - w t ω) α)
    (h_adapted : ∃ R : NNReal,
      StronglyAdapted ℱfil (fun t ω => f (w t ω))
        ∧ (∀ t, ℙ[fun ω => f (w (t + 1) ω) | ℱfil t] ≤ᵐ[ℙ] (fun ω => f (w t ω)))
        ∧ (∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R))
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ) :
    ZSharpObjectiveAsConvergence f w := by
  exact zsharp_heavy_tail_convergence_of_alpha_stable f w η ℱ ℱfil α h_alpha
    h_rm h_stable h_adapted h_meas h_int

end LeanSharp.Tests
