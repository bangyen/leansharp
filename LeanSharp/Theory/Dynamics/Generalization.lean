/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Core.Landscape
import LeanSharp.Core.Objective
import LeanSharp.Core.Taylor.SamBounds
import LeanSharp.Theory.Dynamics.SamBound
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Generalization & Sharpness

This module formalizes the link between the geometric "sharpness" of the loss
landscape and the statistical generalization performance of the model.

## Main definitions

* `PacBayesSharpnessBound`: A PAC-Bayes bound incorporating sharpness.

## Main theorems

* `sam_concrete_generalization`: Connects population risk to empirical risk via
  sharpness and Taylor expansion.
-/

namespace LeanSharp

open Real NNReal

variable {ι : Type*} [Fintype ι]

/-- A simplified PAC-Bayes Generalization Bound incorporating Sharpness. -/
def PacBayesSharpnessBound (L_D L_S : W ι → ℝ) (w : W ι) (ρ : ℝ) (C : ℝ) : Prop :=
  L_D w ≤ L_S w + ‖gradient L_S w‖ * ρ + C

/-- **SAM Generalization Theorem**: Links the population risk to the empirical risk
via the Taylor bound proved in `Taylor.lean`.

This uses the exact `samObjective` we formalized previously. -/
theorem sam_concrete_generalization (L_D : W ι → ℝ) (L_S : SmoothObjective ι) (w : W ι)
    (ρ : ℝ) (C : ℝ) (hρ : 0 ≤ ρ)
    (h_gen : L_D w ≤ samObjective L_S.toFun w ρ + C) :
    L_D w ≤ L_S.toFun w + ‖gradient L_S.toFun w‖ * ρ +
      (L_S.smoothness : ℝ) / 2 * ρ ^ 2 + C := by
  calc L_D w
    _ ≤ samObjective L_S.toFun w ρ + C := h_gen
    _ ≤ L_S.toFun w + ‖gradient L_S.toFun w‖ * ρ +
        (L_S.smoothness : ℝ) / 2 * ρ ^ 2 + C := by
      linarith [sam_taylor_bound L_S w ρ hρ]

end LeanSharp
