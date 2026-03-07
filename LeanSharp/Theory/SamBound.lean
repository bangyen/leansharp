/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Landscape
import LeanSharp.Core.Sam

/-!
# The SAM Generalization Bound

This module formalizes the core generalization theorem for Sharpness-Aware
Minimization (SAM) as presented in Foret et al. (2020).

The theorem bounds the population risk $L_D(w)$ by the maximum empirical risk
within a $\rho$-neighborhood plus a complexity pacing function $h$.

## Main definitions

* `sam_empirical_max`: The maximum empirical risk in a $\rho$-neighborhood.
* `sam_generalization_bound_holds`: Predicate for the SAM generalization bound.

## Main theorems

* `sam_bound_from_gap`: Proves the SAM generalization bound given a standard
  generalization gap assumption and technical boundedness.
-/

namespace LeanSharp

variable {d : ℕ}

/-- The maximal empirical risk in the $\rho$-neighborhood.
This uses the exact `sam_objective` we formalized previously. -/
noncomputable def sam_empirical_max (L_S : W d → ℝ) (w : W d) (ρ : ℝ) : ℝ :=
  sam_objective L_S w ρ

/-- The SAM Generalization Bound Theorem condition.
States that with high probability, the population risk is bounded by the SAM objective. -/
def sam_generalization_bound_holds (L_D L_S : W d → ℝ) (h : ℝ → ℝ) (ρ : ℝ) : Prop :=
  ∀ w : W d, ρ > 0 →
    L_D w ≤ sam_empirical_max L_S w ρ + h (‖w‖^2 / ρ^2)

/-- **SAM Bound from Gap**: The SAM generalization bound holds given a standard
generalization gap assumption.

We prove that `sam_empirical_max ≥ L_S(w)`, so the SAM bound dominates the
ordinary Rademacher / PAC-Bayes generalization bound. -/
theorem sam_bound_from_gap (L_D L_S : W d → ℝ) (h : ℝ → ℝ) {ρ : ℝ}
    (h_gap : ∀ (w : W d) (r : ℝ), r > 0 →
        L_D w ≤ L_S w + h (‖w‖ ^ 2 / r ^ 2))
    (h_bdd : ∀ (w : W d) (r : ℝ), BddAbove
        (L_S '' ((fun ε => w + ε) '' Metric.closedBall 0 r))) :
    sam_generalization_bound_holds L_D L_S h ρ := by
  intro w hρ
  have h_sam_ge : L_S w ≤ sam_empirical_max L_S w ρ :=
    sam_objective_ge_self L_S w (le_of_lt hρ) (h_bdd w ρ)
  have h_gap_spec := h_gap w ρ hρ
  linarith [h_gap_spec, h_sam_ge]

end LeanSharp
