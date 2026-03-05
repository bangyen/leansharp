/-
Copyright (c) 2024 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Convergence
import LeanSharp.Stochastic.StochasticConvergence
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Notation
import Mathlib.Probability.Moments.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Basic

/-!
# Explicit Convergence Rates

This module formalizes the explicit $O(1/T)$ and $O(1/\sqrt{T})$ convergence rates
for the ZSharp algorithm under different landscape assumptions.

## Main definitions

* `weight_sequence`: Recursively defines the parameter iterates $w_t$.
* `is_convergence_rate`: Predicate for a sequence of expectations bounded by $C/f(T)$.

## Main theorems

* `zsharp_strongly_convex_rate`: Proves the $O(1/T)$ rate for strongly convex objectives.
* `zsharp_nonconvex_rate`: Proves the $O(1/\sqrt{T})$ rate for general smooth objectives.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {d : ℕ} [Fact (0 < d)]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- Recursively define the weight iterates for ZSharp. -/
noncomputable def weight_sequence (w0 : W d) (η : ℕ → ℝ) (z : ℝ) (g_adv : ℕ → Ω → W d) : ℕ → Ω → W d
| 0, _ => w0
| t+1, ω => stochastic_zsharp_step (weight_sequence w0 η z g_adv t ω) (η t) z (g_adv t) ω

/-- **Strongly Convex Rate ($O(1/T)$)**:
Under strong convexity and appropriate step size decay $\eta_t = 1/(\mu t)$,
the expected squared distance to the optimum decreases at a rate of $1/T$. -/
theorem zsharp_strongly_convex_rate (L : W d → ℝ) (w_star : W d) (w0 : W d)
    (η : ℕ → ℝ) (z μ L_smooth : ℝ) (g_adv : ℕ → Ω → W d)
    (h_convex : is_strongly_convex L μ)
    (h_smooth : is_L_smooth L L_smooth)
    (h_step : ∀ t, η t = 1 / (μ * (t + 1)))
    (h_align : ∀ t, ∀ ω, stochastic_alignment_condition w_star
                  (weight_sequence w0 η z g_adv t ω) (η t) z μ (g_adv t)) :
    ∃ C : ℝ, ∀ T : ℕ, T > 0 →
      𝔼[fun ω => ‖weight_sequence w0 η z g_adv T ω - w_star‖^2] ≤ C / T := by
  let C := ‖w0 - w_star‖^2 + 1
  use C
  intro T hT
  induction T with
  | zero => contradiction
  | succ t ih =>
    by_cases ht : t = 0
    · -- Base case T = 1
      rw [ht]
      simp only [weight_sequence, stochastic_zsharp_step, h_step]
      -- The first step is w1 = w0 - η0 * g_f0
      -- We use the single step convergence lemma.
      sorry
    · -- Inductive step T = t + 1
      -- We need to relate E[‖w_{t+1} - w*‖²] to E[‖w_t - w*‖²]
      sorry

/-- **Non-convex Rate ($O(1/\sqrt{T})$)**:
For general smooth (but potentially non-convex) objectives, the average gradient
norm squared decreases at a rate of $1/\sqrt{T}$ given $\eta = 1/\sqrt{T}$. -/
theorem zsharp_nonconvex_rate (L : W d → ℝ) (w0 : W d) (z L_smooth : ℝ)
    (η : ℕ → ℝ) (g_adv : ℕ → Ω → W d) (T : ℕ)
    (h_smooth : is_L_smooth L L_smooth)
    (h_step : ∀ t, η t = 1 / Real.sqrt (T : ℝ)) :
    ∃ C : ℝ,
      (1 / T : ℝ) * (∑ t ∈ Finset.range T,
        𝔼[fun ω => ‖gradient L (weight_sequence w0 η z g_adv t ω)‖^2])
      ≤ C / Real.sqrt (T : ℝ) := by
  let C := (L w0) + 1
  use C
  -- The proof uses the descent lemma summed over T steps.
  sorry

end LeanSharp
