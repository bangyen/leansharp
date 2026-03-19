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

end LeanSharp.Tests
