/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Examples.QuadraticBowl
import LeanSharp.Stochastic.Rate

/-!
# O(1/T) Rate Tests

This module instantiates the headline `stochastic_zsharp_rate_O1_T` result on the
quadratic-bowl landscape, demonstrating that the $O(1/T)$ rate claim fires on a
concrete example with the canonical $\eta_t = 1 / (\mu (t+1))$ schedule.

## Examples

* `quadratic_bowl_O1_T_rate`.
-/

namespace LeanSharp.Tests

open LeanSharp.QuadraticBowl
open ProbabilityTheory MeasureTheory

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

local notation "W2" => W (Fin 2)

/-- The $O(1/T)$ rate specializes to the quadratic bowl with optimal point $w^* = 0$:
the expected squared distance to the optimum decays as $(‖w_0‖^2 + 1) / T$ under the
canonical strongly-convex schedule. -/
example (η : ℕ → ℝ) (z μ : ℝ) (g_adv : ℕ → Ω → W2) (ℱ : ℕ → MeasurableSpace Ω)
    (h_le : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_cond_bound : ∀ t, ∀ᵐ ω ∂volume,
      volume[fun ω' =>
        ‖weightSequence wInit η z g_adv (t + 1) ω' - 0‖ ^ 2 | ℱ t] ω ≤
      (1 - η t * μ) * ‖weightSequence wInit η z g_adv t ω - 0‖ ^ 2)
    (hμ : 0 < μ)
    (h_step : ∀ t, η t = 1 / (μ * (t + 1)))
    (h_align0 : StochasticAlignmentCondition (Ω := Ω) wInit 0 (g_adv 0) (η 0) μ z)
    (h_int : ∀ t, Integrable (fun ω => ‖weightSequence wInit η z g_adv t ω - 0‖ ^ 2)) :
    ∀ T : ℕ, T > 0 →
      𝔼[fun ω => ‖weightSequence wInit η z g_adv T ω - 0‖ ^ 2]
        ≤ (‖wInit - 0‖ ^ 2 + 1) / T := by
  exact stochastic_zsharp_rate_O1_T 0 wInit η z μ g_adv ℱ h_le h_cond_bound hμ h_step h_align0 h_int

/-- The $O(1/T)$ rate also holds when the alignment hypothesis is derived from a
deterministic geometric condition via the alignment bridge. -/
example (L : W2 → ℝ) (η : ℕ → ℝ) (z μ L_smooth : ℝ)
    (g_adv : ℕ → Ω → W2) (ℱ : ℕ → MeasurableSpace Ω) (ε : W2)
    (h_le : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_cond_bound : ∀ t, ∀ᵐ ω ∂volume,
      volume[fun ω' =>
        ‖weightSequence wInit η z g_adv (t + 1) ω' - 0‖ ^ 2 | ℱ t] ω ≤
      (1 - η t * μ) * ‖weightSequence wInit η z g_adv t ω - 0‖ ^ 2)
    (hμ : 0 < μ)
    (h_step : ∀ t, η t = 1 / (μ * (t + 1)))
    (h_g0 : g_adv 0 = fun _ => gradient L (wInit + ε))
    (h_align_det : AlignmentCondition wInit 0
      (filteredGradient (gradient L (wInit + ε)) z) μ L_smooth)
    (h_tight : η 0 * L_smooth ^ 2 ≤ μ)
    (h_eta : 0 ≤ η 0)
    (h_int : ∀ t, Integrable (fun ω => ‖weightSequence wInit η z g_adv t ω - 0‖ ^ 2)) :
    ∀ T : ℕ, T > 0 →
      𝔼[fun ω => ‖weightSequence wInit η z g_adv T ω - 0‖ ^ 2]
        ≤ (‖wInit - 0‖ ^ 2 + 1) / T := by
  exact stochastic_zsharp_rate_O1_T_of_deterministic_alignment L 0 wInit η z μ L_smooth
    g_adv ℱ ε h_le h_cond_bound hμ h_step h_g0 h_align_det h_tight h_eta h_int

end LeanSharp.Tests
