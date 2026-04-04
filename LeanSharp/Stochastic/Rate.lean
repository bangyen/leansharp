/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Foundations.Schedules.StronglyConvex

/-!
# Stochastic ZSharp Process - Convergence Rate

This module establishes the final $O(1/T)$ rate theorem for strongly convex objectives.
It re-exports the foundational strongly-convex rate to provide the core point of entry
for downstream objective convergence guarantees.

## Main Theorems

* `stochastic_zsharp_rate_O1_T`: Expected squared distance to optimal weights decays as $1/T$.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- **Theorem: ZSharp $O(1/T)$ Convergence Rate**:
For models satisfying strongly convex stochastic descent constraints, the expected distance
to the optimal weights $w^*$ decays strictly at the $O(1/T)$ rate under the canonical
schedule $\eta_t = 1 / (\mu (t+1))$. -/
theorem stochastic_zsharp_rate_O1_T
    (w_star : W ι) (w0 : W ι)
    (η : ℕ → ℝ) (z μ : ℝ) (g_adv : ℕ → Ω → W ι)
    (ℱ : ℕ → MeasurableSpace Ω)
    (h_le : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_cond_bound : ∀ t, ∀ᵐ ω ∂volume,
      volume[fun ω' =>
        ‖weightSequence w0 η z g_adv (t + 1) ω' - w_star‖ ^ 2 | ℱ t] ω ≤
      (1 - η t * μ) * ‖weightSequence w0 η z g_adv t ω - w_star‖ ^ 2)
    (hμ : 0 < μ)
    (h_step : ∀ t, η t = 1 / (μ * (t + 1)))
    (h_align0 : StochasticAlignmentCondition w0 w_star (g_adv 0) (η 0) μ z)
    (h_int : ∀ t, Integrable (fun ω => ‖weightSequence w0 η z g_adv t ω - w_star‖ ^ 2)) :
    ∀ T : ℕ, T > 0 →
      𝔼[fun ω => ‖weightSequence w0 η z g_adv T ω - w_star‖ ^ 2]
        ≤ (‖w0 - w_star‖ ^ 2 + 1) / T :=
  zsharp_strongly_convex_rate w_star w0 η z μ g_adv ℱ h_le h_cond_bound hμ h_step h_align0 h_int

end LeanSharp
