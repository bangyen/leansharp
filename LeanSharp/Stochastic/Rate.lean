/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Foundations.Schedules.StronglyConvex
import LeanSharp.Theory.Alignment

/-!
# Stochastic ZSharp Process - Convergence Rate

This module establishes the final $O(1/T)$ rate theorem for strongly convex objectives.
It re-exports the foundational strongly-convex rate to provide the core point of entry
for downstream objective convergence guarantees.

## Main Theorems

* `stochastic_zsharp_rate_O1_T`: Expected squared distance to optimal weights decays as $1/T$.
* `stochastic_zsharp_rate_O1_T_of_deterministic_alignment`: The $O(1/T)$ rate with the
  alignment hypothesis derived from a deterministic geometric condition via the bridge.
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

/-- **O(1/T) rate with bridge-derived alignment**: the same rate holds when the
stochastic alignment hypothesis is derived from a deterministic geometric condition
via `deterministic_implies_stochastic_alignment`. This completes the wiring of the
alignment bridges into the rate theorems. -/
theorem stochastic_zsharp_rate_O1_T_of_deterministic_alignment
    (L : W ι → ℝ) (w_star w0 : W ι) (η : ℕ → ℝ) (z μ L_smooth : ℝ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω) (ε : W ι)
    (h_le : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_cond_bound : ∀ t, ∀ᵐ ω ∂volume,
      volume[fun ω' =>
        ‖weightSequence w0 η z g_adv (t + 1) ω' - w_star‖ ^ 2 | ℱ t] ω ≤
      (1 - η t * μ) * ‖weightSequence w0 η z g_adv t ω - w_star‖ ^ 2)
    (hμ : 0 < μ)
    (h_step : ∀ t, η t = 1 / (μ * (t + 1)))
    (h_g0 : g_adv 0 = fun _ => gradient L (w0 + ε))
    (h_align_det : AlignmentCondition w0 w_star
      (filteredGradient (gradient L (w0 + ε)) z) μ L_smooth)
    (h_tight : η 0 * L_smooth ^ 2 ≤ μ)
    (h_eta : 0 ≤ η 0)
    (h_int : ∀ t, Integrable (fun ω => ‖weightSequence w0 η z g_adv t ω - w_star‖ ^ 2)) :
    ∀ T : ℕ, T > 0 →
      𝔼[fun ω => ‖weightSequence w0 η z g_adv T ω - w_star‖ ^ 2]
        ≤ (‖w0 - w_star‖ ^ 2 + 1) / T := by
  have h_align0 : StochasticAlignmentCondition (Ω := Ω) w0 w_star (g_adv 0) (η 0) μ z := by
    rw [h_g0]
    exact deterministic_implies_stochastic_alignment (Ω := Ω) L w0 w_star ε z μ L_smooth η 0
      h_align_det h_tight h_eta
  exact stochastic_zsharp_rate_O1_T w_star w0 η z μ g_adv ℱ h_le h_cond_bound hμ h_step
    h_align0 h_int

end LeanSharp
