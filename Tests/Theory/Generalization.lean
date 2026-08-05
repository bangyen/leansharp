/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Objective
import LeanSharp.Examples.QuadraticBowl
import LeanSharp.Theory.Dynamics.Generalization
import LeanSharp.Theory.Dynamics.SamBound

/-!
# Generalization Theory Tests

This module verifies properties of PAC-Bayes sharpness bounds and SAM objectives.

## Examples
-/

namespace LeanSharp.Tests

open LeanSharp.QuadraticBowl

/-- Test: SAM objective is always greater than or equal to the original objective. -/
example {m : ℕ} (f : W (Fin m) → ℝ) (r : ℝ) (w : W (Fin m))
    (hr : r ≥ 0)
    (h_bdd : BddAbove (f '' ((fun ε => w + ε) '' perturbationNeighborhood r))) :
    samObjective f w r ≥ f w := by
  exact sam_objective_ge_self f w hr h_bdd

/-- Test: SAM objective non-negativity if the original objective is non-negative. -/
example {m : ℕ} (f : W (Fin m) → ℝ) (r : ℝ) (w : W (Fin m))
    (hf : ∀ x, f x ≥ 0) (hr : r ≥ 0)
    (h_bdd : BddAbove (f '' ((fun ε => w + ε) '' perturbationNeighborhood r))) :
    samObjective f w r ≥ 0 := by
  have hsam : f w ≤ samObjective f w r := sam_objective_ge_self f w hr h_bdd
  have hw_nonneg : 0 ≤ f w := hf w
  have hsam_nonneg : 0 ≤ samObjective f w r := le_trans hw_nonneg hsam
  simpa only [ge_iff_le] using hsam_nonneg

/-- The Foret-style SAM generalization bound specializes to the quadratic bowl:
given a generalization gap, the population risk is bounded by the SAM objective
plus a complexity pacing term. -/
example (L_D : W (Fin 2) → ℝ) (h : ℝ → ℝ) (ρ : ℝ)
    (h_gap : ∀ w : W (Fin 2), ρ > 0 →
      L_D w ≤ toyLoss w + h (‖w‖ ^ 2 / ρ ^ 2))
    (h_bdd : ∀ w : W (Fin 2), BddAbove
      (toyLoss '' ((fun ε => w + ε) '' Metric.closedBall 0 ρ))) :
    SamGeneralizationBoundHolds L_D toyLoss h ρ := by
  exact sam_bound_from_gap L_D toyLoss h h_gap h_bdd

/-- The concrete sharpness generalization bound specializes to the quadratic bowl:
population risk is bounded by empirical risk plus the gradient-sharpness and
curvature terms from the Taylor expansion. -/
example (L_D : W (Fin 2) → ℝ) (w : W (Fin 2)) (ρ C : ℝ) (hρ : 0 ≤ ρ)
    (h_gen : L_D w ≤ samObjective toyLoss w ρ + C) :
    L_D w ≤ toyLoss w + ‖gradient toyLoss w‖ * ρ + (2 : ℝ) / 2 * ρ ^ 2 + C := by
  let L_S : SmoothObjective (Fin 2) := {
    toFun := toyLoss
    smoothness := 2
    differentiable := fun _ => (hasFDerivAt_toyLoss _).differentiableAt
    lipschitz := by
      apply LipschitzWith.of_dist_le_mul
      intro w' v
      simpa only [dist_eq_norm] using toy_L_smooth.2 w' v
  }
  exact sam_concrete_generalization L_D L_S w ρ C hρ h_gen

end LeanSharp.Tests
