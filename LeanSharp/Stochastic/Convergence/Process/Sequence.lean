/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Convergence.Process.Descent
import Mathlib.Tactic.Linarith

/-!
# Stochastic ZSharp Process - Sequence Bounds

This module aggregates individual descent steps into sequence-level bounds
governing the entire optimization trajectory.

## Main Theorems
* `stochastic_zsharp_sequence_descent`: Accumulation of descent steps over time.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory NNReal

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- **ZSharp Sequence Descent**:
Aggregates the individual descent steps into a sequence-level bound.
This is the fundamental lemma used to prove the $O(1/\sqrt{T})$ convergence rate. -/
theorem stochastic_zsharp_sequence_descent (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ) (T : ℕ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω)
    (h_step : ∀ t, ∀ᵐ ω ∂ℙ,
      w (t + 1) ω = stochasticZSharpStep (w t ω) η t z (g_adv t) ω)
    (h_desc_step : ∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochasticZSharpStep (w t ω') η t z (g_adv t) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq)
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ)
    (h_int_grad : ∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2) ℙ)
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace) :
    (∑ t ∈ Finset.range T, (η t / 4) * 𝔼[fun ω => ‖gradient f (w t ω)‖ ^ 2]) ≤
      𝔼[fun ω => f (w 0 ω)] - 𝔼[fun ω => f (w T ω)] +
      (∑ t ∈ Finset.range T, (η t ^ 2 * L_smooth / 2) * σsq) := by
  induction T with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, sub_self, add_zero]
      exact le_refl _
  | succ t ih =>
      have h_sum1 :
          (∑ k ∈ Finset.range (t + 1),
            (η k / 4) * ∫ ω, ‖gradient f (w k ω)‖ ^ 2 ∂ℙ) =
          (∑ k ∈ Finset.range t, (η k / 4) * ∫ ω, ‖gradient f (w k ω)‖ ^ 2 ∂ℙ) +
          (η t / 4) * ∫ ω, ‖gradient f (w t ω)‖ ^ 2 ∂ℙ := Finset.sum_range_succ _ _
      have h_sum2 : (∑ k ∈ Finset.range (t + 1), (η k ^ 2 * L_smooth / 2) * σsq) =
          (∑ k ∈ Finset.range t, (η k ^ 2 * L_smooth / 2) * σsq) +
          (η t ^ 2 * L_smooth / 2) * σsq := Finset.sum_range_succ _ _
      have h_exp_step : ∫ ω, f (w (t + 1) ω) ∂ℙ ≤
          ∫ ω, f (w t ω) ∂ℙ - (η t / 4) * ∫ ω, ‖gradient f (w t ω)‖ ^ 2 ∂ℙ +
          (η t ^ 2 * L_smooth / 2) * σsq :=
        stochastic_expected_descent_step L_smooth f w η z σsq t g_adv ℱ
          (h_step t) (h_desc_step t) (h_int t) (h_int_grad t) (h_meas t)
      linarith

end LeanSharp
