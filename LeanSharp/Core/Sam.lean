/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Landscape
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Sharpness-Aware Minimization (SAM)

This module defines the SAM objective function and the perturbation vector.
SAM seek to minimize the maximum loss within a neighborhood of radius `ρ`.

## Main definitions

* `perturbation_neighborhood`: The closed ball of radius `ρ` around the origin.
* `sam_objective`: The maximum loss in the perturbation neighborhood.
* `sam_perturbation`: The first-order approximation of the optimal perturbation.

## Implementation notes

The SAM objective is defined generically using a supremum over the perturbation
neighborhood image. The first-order perturbation is derived as a scaled version
of the gradient.
-/

namespace LeanSharp

variable {ι : Type*} [Fintype ι]

/-- The SAM perturbation neighborhood. We consider all vectors `ε` such that
the L2 norm metric distance `dist 0 ε ≤ ρ`. -/
def perturbation_neighborhood (ρ : ℝ) : Set (W ι) :=
  Metric.closedBall 0 ρ

/-- In SAM, the optimal perturbation `ε*(w)` is the one that maximizes `L(w + ε)`.
To formalize this generically without computing the exact `sup`, we can define
the SAM objective as the supremum over the closed ball. -/
noncomputable def sam_objective (L : W ι → ℝ) (w : W ι) (ρ : ℝ) : ℝ :=
  sSup (L '' ((fun ε => w + ε) '' perturbation_neighborhood ρ))

/-- The exact first-order approximation perturbation `ε*(w)`. -/
noncomputable def sam_perturbation (L : W ι → ℝ) (w : W ι) (ρ : ℝ) : W ι :=
  let g := gradient L w
  let norm_g := ‖g‖
  if norm_g = 0 then 0 else (ρ / norm_g) • g

/-- **SAM Objective Supremum Property**: The SAM objective at point `w` is always
greater than or equal to the base loss `L w`, provided the neighborhood is
bounded above. -/
theorem sam_objective_ge_self (L : W ι → ℝ) (w : W ι) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h_bdd : BddAbove (L '' ((fun ε => w + ε) '' perturbation_neighborhood ρ))) :
    L w ≤ sam_objective L w ρ := by
  unfold sam_objective perturbation_neighborhood
  refine le_csSup h_bdd ⟨w, ⟨0, by simp [Metric.mem_closedBall, hρ], by simp⟩, rfl⟩

end LeanSharp
