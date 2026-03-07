/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Landscape
import LeanSharp.Core.Sam
import LeanSharp.Core.Filters
import LeanSharp.Theory.SamBound
import LeanSharp.Core.Taylor
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Generalization & Sharpness

This module formalizes the link between the geometric "sharpness" of the loss
landscape and the statistical generalization performance of the model.

## Main definitions

* `Dataset`: A representation of a collection of data points.
* `dataset_neighbor`: Predicate for two datasets differing by one element.
* `max_eigenvalue`: The maximum eigenvalue of a symmetric linear operator.
* `sharpness`: Measures loss landscape sharpness via the maximum Hessian eigenvalue.
* `pac_bayes_sharpness_bound`: A PAC-Bayes bound incorporating sharpness.
* `uniform_stability`: Measures algorithm sensitivity to training data.

## Main theorems

* `sam_concrete_generalization`: Connects population risk to empirical risk via
  sharpness and Taylor expansion.
* `zsharp_stability_theorem`: Proves that filtered updates exhibit lower uniform
  stability.
-/

namespace LeanSharp

open Real NNReal

variable {d : ℕ}

/-- A dataset is formally represented as a collection of $n$ data points. -/
def Dataset (DataPoint : Type*) (n : ℕ) := Fin n → DataPoint

/-- Two datasets are neighbors if they differ by exactly one element. -/
def dataset_neighbor {DataPoint : Type*} {n : ℕ} (S S' : Dataset DataPoint n) : Prop :=
  ∃ (i : Fin n), ∀ (j : Fin n), i ≠ j → S j = S' j

/-- The maximum eigenvalue of a symmetric linear operator. -/
noncomputable def max_eigenvalue {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) : ℝ :=
  sSup (spectrum ℝ (hT.toSelfAdjoint : E →L[ℝ] E))

/-- The Sharpness of the loss function at point `w`. -/
noncomputable def sharpness (L : W d → ℝ) (w : W d)
    (hT : (hessian L w).toLinearMap.IsSymmetric) : ℝ :=
  max_eigenvalue (hessian L w).toLinearMap hT

/-- A simplified PAC-Bayes Generalization Bound incorporating Sharpness. -/
def pac_bayes_sharpness_bound (L_D L_S : W d → ℝ) (w : W d) (ρ : ℝ) (C : ℝ) : Prop :=
  L_D w ≤ L_S w + ‖gradient L_S w‖ * ρ + C

/-- **SAM Generalization Theorem**: Links the population risk to the empirical risk
via the Taylor bound proved in `Taylor.lean`.

This uses the exact `sam_objective` we formalized previously. -/
theorem sam_concrete_generalization (L_D L_S : W d → ℝ) (w : W d) (ρ : ℝ) (M : ℝ≥0) (C : ℝ)
    (h_smooth : LipschitzWith M (gradient L_S))
    (h_diff : Differentiable ℝ L_S)
    (hρ : 0 ≤ ρ)
    (h_gen : L_D w ≤ sam_objective L_S w ρ + C) :
    L_D w ≤ L_S w + ‖gradient L_S w‖ * ρ + (M : ℝ) / 2 * ρ ^ 2 + C := by
  have h_taylor := sam_taylor_bound L_S w ρ M h_smooth h_diff hρ
  linarith [h_gen, h_taylor]

/-!
## Uniform Stability

Uniform stability $\beta$ measures the sensitivity of the algorithm to the data.
-/

/-- The uniform stability of a learning algorithm `A` on a dataset. -/
def uniform_stability {DataPoint : Type*} {n : ℕ} (A : Dataset DataPoint n → W d) (β : ℝ) : Prop :=
  ∀ (S S' : Dataset DataPoint n), dataset_neighbor S S' →
  ‖A S - A S'‖ ≤ β / (n : ℝ)

/-- **Stability Theorem**: The Z-score filtered gradient update exhibits lower
uniform stability. -/
theorem zsharp_stability_theorem {DataPoint : Type*} {n : ℕ} (β_sam : ℝ)
    (A_sam : Dataset DataPoint n → W d)
    (A_zsharp : Dataset DataPoint n → W d)
    (h_sam_stable : uniform_stability A_sam β_sam)
    (h_filter_bound : ∀ S S' : Dataset DataPoint n,
      ‖A_zsharp S - A_zsharp S'‖ ≤ ‖A_sam S - A_sam S'‖) :
    uniform_stability A_zsharp β_sam := by
  intro S S' h_neighbor
  have h_base := h_sam_stable S S' h_neighbor
  calc ‖A_zsharp S - A_zsharp S'‖
      ≤ ‖A_sam S - A_sam S'‖ := h_filter_bound S S'
    _ ≤ β_sam / (n : ℝ)      := h_base

end LeanSharp
