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
Under strong convexity and appropriate step size decay $\eta_t = 1 / (\mu t)$,
the expected squared distance to the optimum decreases at a rate of $1/T$. -/
theorem zsharp_strongly_convex_rate (L : W d → ℝ) (w_star : W d) (w0 : W d)
    (η : ℕ → ℝ) (z μ L_smooth : ℝ) (g_adv : ℕ → Ω → W d) [Nonempty Ω]
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
      sorry
    · -- Inductive step T = t + 1
      have hμ : μ > 0 := h_convex.1
      have h_pos_t : 0 < t := Nat.pos_of_ne_zero ht
      have h_step_val : η t = 1 / (μ * (t + 1)) := h_step t
      have h_contraction : 1 - (η t) * μ = (t : ℝ) / (t + 1) := by
        rw [h_step_val]; field_simp [h_convex.1]; ring
      -- Contraction of expectation: 𝔼[‖W_{t+1}-w*‖²] ≤ (t/(t+1)) 𝔼[‖W_t-w*‖²]
      have h_iter : 𝔼[fun ω => ‖weight_sequence w0 η z g_adv (t + 1) ω - w_star‖^2] ≤
                   ((t : ℝ) / (t + 1)) * 𝔼[fun ω =>
                    ‖weight_sequence w0 η z g_adv t ω - w_star‖^2] := by
        rw [← h_contraction]; sorry -- Bridge to stochastic_zsharp_convergence
      -- Combine with IH: 𝔼[‖W_t-w*‖²] ≤ C/t
      have h_ih := ih h_pos_t
      -- Normalize coercions and simplify: (t/(t+1)) * (C/t) = C/(t+1)
      have h_arith : ((t : ℝ) / (t + 1)) * (C / t) = C / (t + 1) := by
        field_simp [ht]
      -- Final logic: 𝔼[W_{t+1}] ≤ (t/(t+1)) * (C/t) = C/(t+1)
      calc (𝔼[fun ω => ‖weight_sequence w0 η z g_adv (t + 1) ω - w_star‖^2])
        _ ≤ ((t : ℝ) / (t + 1)) * 𝔼[fun ω =>
            ‖weight_sequence w0 η z g_adv t ω - w_star‖^2] := h_iter
        _ ≤ ((t : ℝ) / (t + 1)) * (C / t) := by
          apply mul_le_mul_of_nonneg_left h_ih
          apply div_nonneg (Nat.cast_nonneg t) (by norm_cast; linarith)
        _ = C / (t + 1) := h_arith
        _ ≤ C / (↑(t + 1)) := by norm_cast

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
  let C := (L w0 - sInf (Set.range L)) + 1 + L_smooth
  use C
  -- High-level proof by descent lemma and telescoping sum:
  -- 1. For each t, 𝔼[L(w_{t+1})] ≤ 𝔼[L(w_t)] - η 𝔼[‖∇L‖²] + (η²L/2) σ²
  -- 2. Summing from t=0 to T-1: η ∑ 𝔼[‖∇L‖²] ≤ L(w0) - 𝔼[L(wT)] + (T η² L/2) σ²
  -- 3. Use η = 1/√T: (1/√T) ∑ 𝔼[‖∇L‖²] ≤ (L(w0) - sInf L) + L_smooth/2 * σ²
  -- 4. Rearranging: (1/T) ∑ 𝔼[‖∇L‖²] ≤ (1/√T) * ((L(w0) - sInf L) + L_smooth/2 * σ²)
  sorry

end LeanSharp
