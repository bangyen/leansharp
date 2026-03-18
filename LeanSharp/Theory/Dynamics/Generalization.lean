/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Core.Landscape
import LeanSharp.Core.Objective
import LeanSharp.Core.Taylor
import LeanSharp.Theory.Dynamics.SamBound
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Generalization & Sharpness

This module formalizes the link between the geometric "sharpness" of the loss
landscape and the statistical generalization performance of the model.

## Main definitions

* `Dataset`: A representation of a collection of data points.
* `DatasetNeighbor`: Predicate for two datasets differing by one element.
* `maxEigenvalue`: The maximum eigenvalue of a symmetric linear operator.
* `sharpness`: Measures loss landscape sharpness via the maximum Hessian eigenvalue.
* `PacBayesSharpnessBound`: A PAC-Bayes bound incorporating sharpness.
* `UniformStability`: Measures algorithm sensitivity to training data.

## Main theorems

* `sam_concrete_generalization`: Connects population risk to empirical risk via
  sharpness and Taylor expansion.
-/

namespace LeanSharp

open Real NNReal

variable {ι : Type*} [Fintype ι]

/-- A dataset is formally represented as a collection of $n$ data points. -/
def Dataset (DataPoint : Type*) (n : ℕ) := Fin n → DataPoint

/-- Two datasets are neighbors if they differ by exactly one element. -/
def DatasetNeighbor {DataPoint : Type*} {n : ℕ} (S S' : Dataset DataPoint n) : Prop :=
  ∃ (i : Fin n), ∀ (j : Fin n), i ≠ j → S j = S' j

/-- The maximum eigenvalue of a symmetric linear operator. -/
noncomputable def maxEigenvalue {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) : ℝ :=
  sSup (spectrum ℝ (hT.toSelfAdjoint : E →L[ℝ] E))

/-- The Sharpness of the loss function at point `w`. -/
noncomputable def sharpness (L : W ι → ℝ) (w : W ι)
    (hT : (hessian L w).toLinearMap.IsSymmetric) : ℝ :=
  maxEigenvalue (hessian L w).toLinearMap hT

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

/-!
## Uniform Stability

Uniform stability $\beta$ measures the sensitivity of the algorithm to the data.
-/

/-- The uniform stability of a learning algorithm `A` on a dataset. -/
def UniformStability {DataPoint : Type*} {n : ℕ}
    (A : Dataset DataPoint n → W ι) (β : ℝ) : Prop :=
  ∀ (S S' : Dataset DataPoint n), DatasetNeighbor S S' →
  ‖A S - A S'‖ ≤ β / (n : ℝ)

end LeanSharp
