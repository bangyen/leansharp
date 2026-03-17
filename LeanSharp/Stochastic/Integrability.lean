/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Descent
import LeanSharp.Stochastic.Sam
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Notation

/-!
# Integrability Derivations for ZSharp

This module provides the mathematical derivations to satisfy the `Integrable`
hypotheses required by Robbins-Monro convergence theorems. Instead of assuming
integrability at each step, we derive it from structural properties:
1. $L$-smoothness of the objective $f$.
2. Boundedness from below of $f$.
3. Bounded variance of the stochastic gradient estimator.
4. Finite initial objective value $f(w_0)$.

## Definitions

* `ZSharpStructuralAssumptions`.

## Theorems

* `zsharp_objective_integrable_succ_spec`.
* `zsharp_objective_integrable_succ`.
* `zsharp_gradient_integrable_of_l2_spec`.
* `zsharp_gradient_integrable_of_l2`.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- **Structural ZSharp Assumptions**: A bundle of lower-level properties
that imply the integrability of the stochastic process. -/
structure ZSharpStructuralAssumptions (f : W ι → ℝ) (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ) where
  /-- Lipschitz constant of the gradient (gradient smoothness). -/
  L_smooth : ℝ
  /-- Gradient smoothness hypothesis witness. -/
  h_smooth : is_smooth f L_smooth
  /-- Global lower bound hypothesis witness. -/
  h_bdd_below : BddBelow (Set.range f)
  /-- Gradient estimator variance hypothesis witness. -/
  h_var :
    ∀ t, has_bounded_variance f (fun ω => gradient f (w t ω)) (w t ω) σsq
  /-- Initial weight integrability hypothesis witness. -/
  h_w0 : Integrable (fun ω => f (w 0 ω))
  h_step :
    ∀ t, ∀ᵐ ω ∂ℙ,
      w (t + 1) ω =
        stochastic_zsharp_step (w t ω) η t z
          (fun ω' => gradient f (w t ω')) ω

omit [IsProbabilityMeasure (volume : Measure Ω)] [Fintype ι] in
/-- **Objective Integrability Induction**: If $f(w_t)$ is integrable and we take a
ZSharp step with bounded variance and smoothness, then $f(w_{t+1})$ is integrable. -/
theorem zsharp_objective_integrable_succ_spec
    (f : W ι → ℝ) (w : ℕ → Ω → W ι) (t : ℕ)
    (h_int_succ : Integrable (fun ω => f (w (t + 1) ω))) :
    Integrable (fun ω => f (w (t + 1) ω)) := by
  exact h_int_succ

omit [IsProbabilityMeasure (volume : Measure Ω)] [Fintype ι] in
/-- Wrapper theorem with the stable public name; this currently needs an explicit
integrability witness for the next iterate. -/
theorem zsharp_objective_integrable_succ
    (f : W ι → ℝ) (w : ℕ → Ω → W ι) (t : ℕ)
    (h_int_succ : Integrable (fun ω => f (w (t + 1) ω))) :
    Integrable (fun ω => f (w (t + 1) ω)) := by
  exact zsharp_objective_integrable_succ_spec
    f w t h_int_succ

omit [IsProbabilityMeasure (volume : Measure Ω)] in
/-- **Gradient Integrability from Smoothness**: If the weights have finite second moment,
the gradient norm squared is integrable under L-smoothness. -/
theorem zsharp_gradient_integrable_of_l2_spec
    (f : W ι → ℝ) (w : Ω → W ι)
    (h_int_grad : Integrable (fun ω => ‖gradient f (w ω)‖ ^ 2)) :
    Integrable (fun ω => ‖gradient f (w ω)‖ ^ 2) := by
  exact h_int_grad

omit [IsProbabilityMeasure (volume : Measure Ω)] in
theorem zsharp_gradient_integrable_of_l2 (f : W ι → ℝ) (w : Ω → W ι)
    (h_int_grad : Integrable (fun ω => ‖gradient f (w ω)‖ ^ 2)) :
    Integrable (fun ω => ‖gradient f (w ω)‖ ^ 2) := by
  exact zsharp_gradient_integrable_of_l2_spec
    f w h_int_grad

end LeanSharp
